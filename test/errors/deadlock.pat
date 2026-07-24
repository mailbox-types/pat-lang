interface Test { Request(), Response() }

def proc1(self: Test?, other: Test!): Unit {
    guard self : Request {
        receive Request() from self ->
            other ! Response();
            free(self)
    }
}

def proc2(self: Test?, other: Test!): Unit {
    guard self : Response {
        receive Response() from self ->
            other ! Request();
            free(self)
    }
}

def main(): Unit {
    let mb1 = new[Test] in
    let mb2 = new[Test] in
    spawn { proc1(mb1, mb2) };
    spawn { proc2(mb2, mb1) }
}

main()
