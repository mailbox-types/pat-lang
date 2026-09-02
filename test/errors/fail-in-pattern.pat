# The message being received IS in the guard pattern, so after the receive the
# residual pattern is 1, not 0, and the mailbox is not unreliable.

interface Test { Foo(), Bar() }

def bad(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> fail(x)
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    bad(m)
}

main()
