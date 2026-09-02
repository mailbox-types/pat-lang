# Guard bodies are checked against the expected type rather than synthesised,
# so a bare `fail` needs no annotation in any branch position -- including the
# first, which used to be the one that had to be synthesisable.

interface Test { Foo(), Bar() }

def fail_last(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        receive Bar() from x -> fail(x)
    }
}

def fail_first(x: Test?): Int {
    guard x : Foo {
        receive Bar() from x -> fail(x)
        receive Foo() from x -> free(x); 7
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    fail_last(m);
    let n = new[Test] in
    n ! Foo();
    print(intToString(fail_first(n)))
}

main()
