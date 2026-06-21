interface WaitingRoom { Enter(Customer!), Next(Barber!), Sleeping(Barber!),
    WaitingCustomer(Customer!), PendingCustomer(Customer!) }
interface Customer { Start(), Full(), Wait(), Done() }
interface Barber { Wake(WaitingRoom!), CustomerReady(Customer!, WaitingRoom!),
    RoomEmpty(WaitingRoom!), Exit() }


### Waiting Room

## In the case that the barber is busy, we are waiting for a Next message,
## and our mailbox can contain many Enter messages and customer messages

## In the case that the barber is asleep, there won't be any waiting customers,
## and any Enter requests will need to transition us back to waitingRoom

## NOTE: This will only work with Erlang-style semantics for pattern matching
## (which would be sensible but isn't the current Pat semantics).
##
## We shouldn't be relying on numCustomers for actually making deisions in
## Next(-) -- no way of tracking the dependency between buffer size and
## numCustomers.
##
## In this case we assume we try and consume Enter and WaitingCustomer messages
## prior to Next messages. The only time we should process a Next message in
## this state is if all Enter and WaitingCustomer requests have already been
## processed.
def waitingRoom(self: WaitingRoom?, numCustomers: Int, capacity: Int): Unit {
    guard self : Enter* . WaitingCustomer* . Next {
        receive Enter(customer) from self ->
            if (numCustomers >= capacity) {
                print("Waiting room full; kicking customer out");
                customer ! Full();
                waitingRoom(self, numCustomers, capacity)
            } else {
                customer ! Wait();
                self ! WaitingCustomer(customer);
                waitingRoom(self, numCustomers + 1, capacity)
            }
        receive WaitingCustomer(customer) from self ->
            self ! PendingCustomer(customer);
            waitingRoomPending(self, numCustomers, capacity)
        receive Next(barber) from self ->
            barber ! RoomEmpty(self);
            guard self : Enter* . WaitingCustomer* . Sleeping {
                receive Sleeping(barber) from self ->
                    waitingRoomSleepingBarber(self, barber, capacity)
            }
    }
}

def waitingRoomPending(self: WaitingRoom?, numCustomers: Int, capacity: Int): Unit {
    guard self : PendingCustomer . Next . (Enter* . WaitingCustomer*)  {
        receive Enter(customer) from self ->
            if (numCustomers >= capacity) {
                print("Waiting room full; kicking customer out");
                customer ! Full();
                waitingRoomPending(self, numCustomers, capacity)
            } else {
                customer ! Wait();
                self ! WaitingCustomer(customer);
                waitingRoomPending(self, numCustomers + 1, capacity)
            }
        receive Next(barber) from self ->
            guard self : PendingCustomer . Enter* . WaitingCustomer* {
                free -> barber ! Exit()
                receive PendingCustomer(customer) from self ->
                    barber ! CustomerReady(customer, self);
                    waitingRoom(self, numCustomers - 1, capacity)
            }
    }
}


# Called when the barber is snoozing (i.e., numWaiting = 0)
def waitingRoomSleepingBarber(self: WaitingRoom?, barber: Barber!, capacity: Int): Unit {
    guard self : Enter* . WaitingCustomer* {
        free -> ()
        receive WaitingCustomer(customer) from self ->
                self ! WaitingCustomer(customer);
                barber ! Wake(self);
                waitingRoom(self, 1, capacity)
        receive Enter(customer) from self ->
                self ! WaitingCustomer(customer);
                customer ! Wait();
                barber ! Wake(self);
                waitingRoom(self, 1, capacity)
    }
}


### Barber

def awakeBarber(self: Barber?): Unit {
    guard self : CustomerReady + RoomEmpty + Exit {
        receive Exit() from self -> free(self)
        receive RoomEmpty(waitingRoom) from self ->
            print("Room empty; going to sleep");
            waitingRoom ! Sleeping(self);
            sleepingBarber(self)
        receive CustomerReady(customer, waitingRoom) from self ->
            customer ! Start();
            print("Cutting hair");
            print("Finished cutting hair; notifying customer and waiting room");
            customer ! Done();
            waitingRoom ! Next(self);
            awakeBarber(self)
    }
}

def sleepingBarber(self: Barber?): Unit {
    guard self : Wake + 1 {
        free -> ()
        receive Wake(waitingRoom) from self ->
            waitingRoom ! Next(self);
            awakeBarber(self)
    }
}


### Customer
def customer(self: Customer?, waitingRoom: WaitingRoom!): Unit {
    waitingRoom ! Enter(self);
    guard self : Full + (Wait.Start.Done) {
        receive Full() from self ->
            print("Room is full. Oh well, best go somewhere else");
            free(self)
        receive Wait() from self ->
            print("Waiting");
            waitingCustomer(self)
    }
}

def waitingCustomer(self: Customer?): Unit {
    guard self : Start.Done {
        receive Start() from self ->
            print("Barber is starting my haircut");
            guard self : Done {
                receive Done() from self ->
                    print("Haircut finished!");
                    free(self)
            }
    }
}


### Main

def main(): Unit {
    let cust1 = new[Customer] in
    let cust2 = new[Customer] in
    let cust3 = new[Customer] in
    let waitingRoom = new[WaitingRoom] in
    let barber = new[Barber] in
    spawn { waitingRoomSleepingBarber(waitingRoom, barber, 10) };
    spawn { sleepingBarber(barber) };
    spawn { customer(cust1, waitingRoom) };
    spawn { customer(cust2, waitingRoom) };
    spawn { customer(cust3, waitingRoom) }
}

main()
