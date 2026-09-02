# `fail` checks against any type, not just Unit.

interface Test { Foo(), Bar() }

def as_int(x: Test?): Int {
    guard x : Foo {
        receive Foo() from x -> free(x); 1
        receive Bar() from x -> fail(x)
    }
}

def as_tuple(x: Test?): (Int * Int) {
    guard x : Foo {
        receive Foo() from x -> free(x); (1, 2)
        receive Bar() from x -> fail(x)
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    print(intToString(as_int(m)));
    let n = new[Test] in
    n ! Foo();
    let (a, b) = as_tuple(n) in
    print(intToString(a + b))
}

main()
