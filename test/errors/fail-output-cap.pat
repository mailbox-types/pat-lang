# `fail` needs a receive capability. An output mailbox reference cannot be
# given the unreliable receive type `?0`.

interface Test { Foo() }

def bad(x: Test!): Unit {
    (fail(x): Unit)
}

def main(): Unit { () }

main()
