# Unlike previous `fail` guard (likely erroneous), the `fail` construct shouldn't
# consume other linear resources.

interface Test { Foo(), Bar() }
interface Other { Ping() }

def bad(x: Test?, y: Other?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x); free(y)
        receive Bar() from x -> fail(x)
    }
}

def main(): Unit {
    let m = new[Test] in
    let o = new[Other] in
    m ! Foo();
    bad(m, o)
}

main()
