# After receiving Foo from a mailbox with pattern Foo.Bar, a Bar is still
# expected. The residual pattern is Bar, not 0, so `fail` is not typable.

interface Test { Foo(), Bar() }

def bad(x: Test?): Unit {
    guard x : Foo . Bar {
        receive Foo() from x -> (fail(x): Unit)
    }
}

def main(): Unit { () }

main()
