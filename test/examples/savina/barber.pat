interface WaitingRoom { Enter(Customer!), Next(Barber!), Sleeping(Barber!) }
interface WaitingRoomBuffer { WaitingCustomer(Customer!) }
interface Customer { Start(), Full(), Wait(), Done() }
interface Barber { Wake(WaitingRoom!), CustomerReady(Customer!, WaitingRoom!), RoomEmpty(WaitingRoom!) }


### Waiting Room

## In the case that the barber is busy, we are waiting for a Next message,
## and our mailbox can contain many Enter messages and customer messages

## In the case that the barber is asleep, there won't be any waiting customers,
## and any Enter requests will need to transition us back to waitingRoom


def waitingRoom(self: WaitingRoom?, customerBuffer: WaitingRoomBuffer?,
                numCustomers: Int, capacity: Int): Unit {
    guard self : Enter* . Next {
        receive Enter(customer) from self ->
            if (numCustomers >= capacity) {
                print("Waiting room full; kicking customer out");
                customer ! Full();
                waitingRoom(self, customerBuffer, numCustomers, capacity)
            } else {
                customerBuffer ! WaitingCustomer(customer);
                customer ! Wait();
                waitingRoom(self, customerBuffer, numCustomers + 1, capacity)
            }
        receive Next(barber) from self ->
            # Receive from customer buffer
            print("Sending next customer to barber");
            guard customerBuffer : WaitingCustomer* {
                free ->
                    # In this case there are no more customers.
                    # Notify the barber that he can sleep; move to sleeping state
                    barber ! RoomEmpty(self);
                    guard self : Enter* . Sleeping {
                        # Receive notification that barber is asleep
                        receive Sleeping(barber) from self ->
                            waitingRoomSleepingBarber(self, barber, capacity)
                    }
                receive WaitingCustomer(customer) from customerBuffer ->
                    barber ! CustomerReady(customer, self);
                    waitingRoom(self, customerBuffer, numCustomers - 1, capacity)
            }
    }
}


# Called when the barber is snoozing (i.e., numWaiting = 0)
def waitingRoomSleepingBarber(self: WaitingRoom?, barber: Barber!, capacity: Int): Unit {
    guard self : Enter* {
        free -> ()
        receive Enter(customer) from self ->
            let buffer = new[WaitingRoomBuffer] in
            buffer ! WaitingCustomer(customer);
            customer ! Wait();
            barber ! Wake(self);
            waitingRoom(self, buffer, 1, capacity)
    }
}


### Barber

def barber(self: Barber?): Unit {
    guard self : CustomerReady + RoomEmpty {
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
            barber(self)
    }
}

def sleepingBarber(self: Barber?): Unit {
    guard self : Wake + 1 {
        free -> ()
        receive Wake(waitingRoom) from self ->
            waitingRoom ! Next(self);
            barber(self)
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
