# The subject of `fail` must be a mailbox.

interface Test { Foo() }

def bad(n: Int): Unit {
    (fail(n): Unit)
}

def main(): Unit { () }

main()
