### non-exhaustive case!
### Task has two constructors (Base and Step), but case
### expression only handles Base. should produce an error

data Task = Base | Step Task Task

def describe(t: Task): Int {
    case t of {
        Base -> 0
    }
}

def main(): Unit { print(intToString(describe(Base))) }
main()
