# Now that `fail` is a construct rather than a guard, a guard expression may
# contain more than one failing branch. The old `fail` guard was capped at one
# ("At most one `fail` guard allowed").

interface Test { Foo(), Bar(), Baz() }

def foo(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        receive Bar() from x -> fail(x)
        receive Baz() from x -> fail(x)
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    foo(m)
}

main()
