interface Test { }
interface Receiver { Enter(Test!1) }

def receiver(mbList: List(Test!), self: Receiver?): Unit {
    guard self : Enter.Enter {
        receive Enter(mb) from self ->
            spawn { receiver2((mb :: mbList), self) }
    }
}

def receiver2(mbList: List(Test!), self: Receiver?): Unit {
    guard self : Enter {
        receive Enter(mb) from self ->
            free(self);
            spawn { receiver3((mb :: mbList)) }
    }
}

def receiver3(mbList: List(Test!)): Unit {
    case mbList: List(Test!) of {
          nil -> ()
        | (x :: xs) ->
            case xs: List(Test!) of {
                nil -> ()
                | (y :: ys) ->
                    # x and y are in scope here as separate names, yet
                    # refer to the same underlying name
                    ()
            }
    }
}

def main(): Unit {
    let mb1 = new[Test] in
    let receiverMb = new[Receiver] in
    spawn { receiver((nil : List(Test!1)), receiverMb) };
    receiverMb ! Enter(mb1);
    receiverMb ! Enter(mb1);
    free(mb1)
}

main()
