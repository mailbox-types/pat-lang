interface Door {
    Want(Int, Robot!),
    Inside(Robot!),
    Prepared(Warehouse!),
    WantLeave(Robot!),
    Outside(),
    TableIdle(Warehouse!)
}

interface Robot {
    GoIn(Door!),
    GoOut(Door!),
    Busy(),
    Delivered(Warehouse!, Door!)
}

interface Warehouse {
    Prepare(Int, Door!),
    Deliver(Robot!, Door!),
    PartTaken()
}

# Door
def freeDoor(self: Door?, warehouse: Warehouse!): Unit {
    guard self : Want* {
        free -> ()
        receive Want(part, robot) from self ->
            robot ! GoIn(self);
            warehouse ! Prepare(part, self);
            busyDoor(self)
    }
}

def busyDoor(self: Door?): Unit {
    guard self : Inside . Prepared . Want* {
        receive Want(partNum, robot) from self ->
            robot ! Busy();
            busyDoor(self)
        receive Inside(robot) from self ->
            guard self : Prepared . Want* {
                receive Prepared(warehouse) from self ->
                    warehouse ! Deliver(robot, self);
                    guard self : WantLeave . TableIdle . Want* {
                        receive WantLeave(robot) from self ->
                            robot ! GoOut(self);
                            finaliseDoor(self, warehouse)
                    }
            }
    }
}

def finaliseDoor(self: Door?, warehouse: Warehouse!): Unit {
    guard self : Outside . TableIdle . Want* {
        receive Outside() from self ->
            guard self : TableIdle . Want* {
                receive TableIdle(warehouse) from self ->
                    freeDoor(self, warehouse)
            }
        receive TableIdle(warehouse) from self ->
            guard self : Outside . Want* {
                receive Outside() from self ->
                    freeDoor(self, warehouse)
            }
    }
}

# Robot
def idleRobot(self: Robot?, door: Door!): Unit {
    door ! Want(0, self);
    guard self : (Busy + GoIn) {
        receive Busy() from self -> free(self)
        receive GoIn(door) from self ->
            door ! Inside(self);
            insideRobot(self)
    }
}

def insideRobot(self: Robot?): Unit {
    let self =
        guard self : Delivered {
            receive Delivered(warehouse, door) from self ->
                warehouse ! PartTaken();
                door ! WantLeave(self);
                self
        }
    in
    guard self : GoOut {
        receive GoOut(door) from self ->
            door ! Outside();
            free(self)
    }
}

# Warehouse
def freeWarehouse(self: Warehouse?): Unit {
    guard self : Prepare + 1 {
        free -> ()
        receive Prepare(partNum, door) from self ->
            door ! Prepared(self);
            preparedWarehouse(self)
    }
}

def preparedWarehouse(self: Warehouse?): Unit {
    guard self : Deliver {
        receive Deliver(robot, door) from self ->
            robot ! Delivered(self, door);
            handlePartTaken(self, door)
    }
}

def handlePartTaken(self: Warehouse?, door: Door!): Unit {
    guard self : PartTaken {
        receive PartTaken() from self ->
            door ! TableIdle(self);
            freeWarehouse(self)
    }
}

def discardList(xs: List(Robot!)) : Unit {
    case xs : List(Robot!) of {
        nil -> ()
        | (a :: as) -> discardList(as)
    }
}

def spawnRobots(numRobots: Int, door: Door!, acc: List(Robot!)): Unit {
    if (numRobots <= 0) {
        discardList(acc)
    } else {
        let newRobot = new[Robot] in
        spawn { idleRobot(newRobot, door) };
        spawnRobots(numRobots - 1, door, (newRobot :: acc))
    }
}

def main(n: Int): Unit {
    let door = new[Door] in
    let warehouse = new[Warehouse] in
    spawn { freeDoor(door, warehouse) };
    spawnRobots(n, door, (nil : List(Robot!)));
    spawn { freeWarehouse(warehouse) }
}

main(3)
