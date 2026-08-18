### Adapted from savina/barber. 
###
### A barber is waiting for customers. When there are no customers the barber sleeps. When a customer
### arrives, he wakes the barber or sits in one of the waiting chairs in the waiting room. If all chairs
### are occupied, the customer leaves. Customers repeatedly visit the barber shop until they get a haircut.
### The key element of the solution is to make sure that whenever a customer or a barber checks the state
### of the waiting room, they always see a valid state. The problem is implemented using a Selector actor
### that decides which is the next customer, Customer actors, a Barber actor and a Room actor.

interface RoomMb {
    Enter(CustomerMb!),
    Next(),
    Exit()
}

interface BarberMb {
    Enter(CustomerMb!, RoomMb!),
    Exit()
}

interface SelectorMb {
    Start(),
    Returned(CustomerMb!)
}

interface CustomerMb {
    Full(RoomMb!),
    Start(RoomMb!),
    Done(),
    Exit()
}

def room(self: RoomMb?, capacity: Int, waiters: List(CustomerMb!), waiting: Int, barber: BarberMb!): Unit {
    guard self: (Enter + Next + Exit)* {
        free -> ()
        receive Enter(customerMb) from self ->
            if (waiting == capacity) {
                customerMb ! Full(self);
                room(self, capacity, waiters, waiting, barber)
            }
            else {
                sleep(5);
                spawn { room(self, capacity, (customerMb :: waiters), (waiting + 1), barber) }
            }
        receive Next() from self ->
            caseL waiters : List(CustomerMb!) of {
                nil ->
                    sleep(5);
                    room(self, capacity, (nil : List(CustomerMb!)), waiting, barber)
                | (a :: as) -> 
                    barber ! Enter(a, self);
                    room(self, capacity, as, (waiting - 1), barber)
            }
        receive Exit() from self ->
            barber ! Exit();
            roomExit(self)
    }
}

def roomExit(self : RoomMb?) : Unit {
    guard self: (Enter + Next + Exit)* {
        free -> ()
        receive Enter(customerMb) from self -> roomExit(self)
        receive Next() from self -> roomExit(self)
        receive Exit() from self -> roomExit(self)
    }
}

def barber(self: BarberMb?): Unit {
    guard self: (Enter + Exit)* {
        free -> ()
        receive Enter(customerMb, roomMb) from self ->
            sleep(10);
            customerMb ! Done();
            roomMb ! Next();
            barber(self)
        receive Exit() from self ->
            barberExit(self)
    }
}

def barberExit(self : BarberMb?) : Unit {
    guard self: (Enter + Exit)* {
        free -> ()
        receive Enter(customerMb, roomMb) from self -> barberExit(self)
        receive Exit() from self -> barberExit(self)
    }
}

def spawnCustomers(self: SelectorMb?, generator: Int, soFar: Int, acc : List(CustomerMb!)): (SelectorMb? * List(CustomerMb!)) {
    if (soFar == generator) {
            (self, acc)
        }
    else {
        let customerMb = new [CustomerMb] in
        spawn { customer(customerMb, self)};
        spawnCustomers(self, generator, (soFar + 1), (customerMb :: acc))
    }
}

def startCustomers(customerMbs : List(CustomerMb!), room : RoomMb!) : Unit {
    caseL customerMbs : List(CustomerMb!) of {
        nil -> ()
        | (a :: as) ->
            a ! Start(room);
            startCustomers(as, room)
    } 
}

def doneCustomers(customerMbs : List(CustomerMb!)) : Unit {
    caseL customerMbs : List(CustomerMb!) of {
        nil -> ()
        | (a :: as) ->
            a ! Done();
            doneCustomers(as)
    } 
}

def selector(self: SelectorMb?, generator: Int, haircuts: Int, target: Int, customers : List(CustomerMb!), room: RoomMb!): Unit {
    guard self: (Start + Returned)* {
        free -> ()
        receive Start() from self ->
            let (self, newCustomers) = spawnCustomers(self, generator, 0, (nil : List(CustomerMb!))) in
            startCustomers(customers, room);
            selector(self, generator, haircuts, target, newCustomers, room)
        receive Returned(customerMb) from self ->
            let newHaircuts = haircuts + 1 in
            if (newHaircuts == target) {
                doneCustomers(customers);
                room ! Exit();
                selectorExit(self)
            }
            else {
                customerMb ! Start(room);
                selector(self, generator, newHaircuts, target, customers, room)
            }
    }
}

def selectorExit(self : SelectorMb?) : Unit {
    guard self: (Start + Returned)* {
        free -> ()
        receive Start() from self -> selectorExit(self)
        receive Returned(customerMb) from self -> selectorExit(self)
    }
}

def customer(self: CustomerMb?, selector: SelectorMb!): Unit {
    guard self: (Full + Start + Done + Exit)* {
        free -> ()
        receive Full(room) from self ->
            sleep(10);
            self ! Start(room);
            customer(self, selector)
        receive Start(room) from self ->
            room ! Enter(self);
            customer(self, selector)
        receive Done() from self ->
            selector ! Returned(self);
            customer(self, selector)
        receive Exit() from self ->
            customerExit(self)
    }
}

def customerExit(self : CustomerMb?) : Unit {
    guard self: (Full + Start + Done + Exit)* {
        free -> ()
        receive Full(room) from self -> customerExit(self)
        receive Start(room) from self -> customerExit(self)
        receive Done() from self -> customerExit(self)
        receive Exit() from self -> customerExit(self)
    }
}

def main() : Unit {
    let barberMb = new [BarberMb] in
    spawn {barber(barberMb)};

    let roomMb = new [RoomMb] in
    spawn {room(roomMb, 2, (nil : List(CustomerMb!)), 0, barberMb)};

    let selectorMb = new [SelectorMb] in
    spawn {selector(selectorMb, 4, 0, 6, (nil : List(CustomerMb!)), roomMb)};

    selectorMb ! Start()
}
