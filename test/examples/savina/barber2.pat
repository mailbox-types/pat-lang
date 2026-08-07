interface WaitingRoom { Enter(Customer!), Next(Barber!), Sleeping(Barber!),
    WaitingCustomer(Customer!) }
interface Customer { Start(), Full(), NoWait(), Wait(), Done() }
interface Barber { Wake(WaitingRoom!), CustomerReady(Customer!, WaitingRoom!),
    RoomEmpty(WaitingRoom!), Exit() }


### Waiting Room

## In the case that the barber is busy, we are waiting for a Next message,
## and our mailbox can contain many Enter messages and customer messages

## In the case that the barber is asleep, there won't be any waiting customers,
## and any Enter requests will need to transition us back to waitingRoom
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
        receive Next(barber) from self ->
            if (numCustomers > 0) {
                guard self : Enter* . WaitingCustomer* {
                    free -> barber ! Exit()
                    receive WaitingCustomer(customer) from self ->
                        barber ! CustomerReady(customer, self);
                        waitingRoom(self, numCustomers - 1, capacity)
                    # Customer has just entered
                    receive Enter(customer) from self ->
                        customer ! NoWait();
                        barber ! CustomerReady(customer, self);
                        waitingRoom(self, numCustomers, capacity)
                }
            } else {
                barber ! RoomEmpty(self);
                guard self : Enter* . WaitingCustomer* . Sleeping {
                    receive Sleeping(barber) from self ->
                        waitingRoomSleepingBarber(self, barber, capacity)
                }
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
    guard self : Full + (NoWait.Start.Done) + (Wait.Start.Done) {
        receive Full() from self ->
            print("Room is full. Oh well, best go somewhere else");
            free(self)
        receive Wait() from self ->
            print("Waiting");
            waitingCustomer(self)
        receive NoWait() from self ->
            print("No need to wait; going to barber");
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
