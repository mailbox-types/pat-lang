##   - two-parameter type: Either a b = Left a | Right b
##   - mailbox types as arguments: Either(Mb![R], Int)
##   - linear resource tracking through user-defined type:
##       mailbox stored in Left(mb) must be consumed exactly once,
##       and type-checker verifies this when we case on result

data Either a b = Left a | Right b

interface Mb {
    Done()
}

## conditionally wraps mailbox or integer
## mailbox mb is linear: must end up in exactly one branch
def choose(flag: Bool, mb: Mb![R]): Either(Mb![R], Int) {
    if (flag) {
        (Left(mb) : Either(Mb![R], Int))
    } else {
        (Right(42) : Either(Mb![R], Int))
    }
}

def main(): Unit {
    let mb = new [Mb] in
    spawn { guard mb : Done { free -> () receive Done() from mb -> free(mb) } };

    ## choose(true, mb) wraps mb in Left; case below sends Done message
    let result = (choose(true, mb) : Either(Mb![R], Int)) in
    case result : Either(Mb![R], Int) of {
        Left(m)  -> m ! Done()   ## consume mailbox: send Done
      | Right(n) -> ()           ## no mailbox in this branch
    }
}

main()

