## Constructor pattern binding the wrong number of variables.
## 'Push' has 2 arguments but the pattern binds 1.

data Stack a = Empty | Push a (Stack a)

def depth(s: Stack(Int)): Int {
    case s of {
        Empty -> 0
      | Push(x) -> 1
    }
}

def main(): Unit {
    print(intToString(depth(Empty)))
}

main()
