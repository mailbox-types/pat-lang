# `fail` requires the unreliable mailbox type `?0`. A mailbox that is known to
# be empty but reliable (`?1`) is not good enough: 1 is not included in 0.

interface Test { Foo() }

def bad(x: Test?1): Unit {
    (fail(x): Unit)
}

def main(): Unit { () }

main()
