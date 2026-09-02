# A well-typed `fail` branch is unreachable by construction: the type system
# proves no message can be waiting. This checks the branch survives the
# reference-counting and evaluation passes without being entered.

interface Test { Foo(), Bar() }

def foo(x: Test?): Int {
    guard x : Foo {
        receive Foo() from x -> free(x); 42
        receive Bar() from x -> (fail(x): Int)
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    print(intToString(foo(m)))
}

main()
