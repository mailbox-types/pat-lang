# As a construct, `fail` can appear in nested expression positions, not just
# as the whole body of a guard branch.

interface Test { Foo(), Bar() }

def foo(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        receive Bar() from x -> print(intToString((fail(x): Int)))
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    foo(m)
}

main()
