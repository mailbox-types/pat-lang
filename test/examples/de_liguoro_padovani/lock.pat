interface Lock { Acquire(User!), Release() }
interface User { Acquired(Lock!) }

def freeLock(self: Lock?): Unit {
    guard self : Acquire*  {
        free -> ()
        receive Acquire(owner) from self ->
            owner ! Acquired(self);
            busyLock(self)
    }
}

def busyLock(self: Lock?): Unit {
    guard self : Acquire* . Release {
        receive Release() from self ->
            freeLock(self)
    }
}

def user(num: Int, lock: Lock!): Unit {
    let self = new[User] in
    lock ! Acquire(self);
    guard self : Acquired {
        receive Acquired(lock) from self ->
            print(intToString(num));
            lock ! Release();
            free(self)
    }
}


def main(): Unit {
    let lock = new[Lock] in
    spawn { freeLock(lock) };
    spawn { user(1, lock) };
    spawn { user(2, lock) }
}


main()
