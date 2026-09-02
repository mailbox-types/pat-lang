# The usual way to reach `?0`: a `receive` guard for a message that the
# guard pattern says cannot be there. The residual pattern is 0, so the
# mailbox is unreliable in that branch and `fail` typechecks.

interface Test { Foo(), Bar() }

def foo(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        receive Bar() from x -> (fail(x): Unit)
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    foo(m)
}

main()
