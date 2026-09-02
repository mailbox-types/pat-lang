# As a construct, `fail` can appear in nested expression positions, not just
# as the whole body of a guard branch.

interface Test { Foo(), Bar() }

def foo(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        # Note: Intuitively this should TC without an annotation.
        # However at present because of let-insertion during IR conversion
        # we end up needing to first let-bind the fail... 
        # Would be good to investigate this more in future and see whether we
        # can remove this.
        receive Bar() from x -> print(intToString((fail(x) : Int)))
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    foo(m)
}

main()
