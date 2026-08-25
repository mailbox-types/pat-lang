## Constructor applied to the wrong number of arguments.
## 'Push' expects 2 arguments but is given 1.

data Stack a = Empty | Push a (Stack a)

def main(): Unit {
    let s = Push(1) in
    ()
}

main()
