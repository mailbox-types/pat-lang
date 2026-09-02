interface Future { Put(Int), Get(User!) }
interface User   { Reply(Int) }

def future(self: Future?): Unit {
    guard self : Put.Get* {
        receive Put(x) from self -> resolvedFuture(self, x)
    }
}

def resolvedFuture(self: Future?, value: Int): Unit {
    guard self : Get* {
        free -> ()
        receive Get(user) from self ->
            user ! Reply(value);
            resolvedFuture(self, value)
        receive Put(x) from self -> fail(self)
    }
}

def user(future: Future!): Int {
    let self = new[User] in
    future ! Get(self);
    guard self : Reply {
        receive Reply(x) from self ->
            free(self);
            x
    }
}

def main(): Unit {
    # Test comment
    let future_mb = new[Future] in
    spawn { future(future_mb) };
    future_mb ! Put(5);
    print(intToString(user(future_mb)));
    print(intToString(user(future_mb)))
}

main()
