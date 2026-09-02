# `fail` is typable exactly when its subject has the unreliable mailbox
# type `?0`. Here the annotation states that directly, with no guard involved.

interface Test { Foo() }

def unreachable(x: Test?0): Unit {
    (fail(x): Unit)
}

def main(): Unit { () }

main()
