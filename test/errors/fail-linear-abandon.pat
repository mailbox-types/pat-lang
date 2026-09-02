# `fail` discharges only its own subject, not every linear resource in scope.
# Here `y` is consumed in the Foo branch but abandoned in the failing branch,
# so it does not appear in every branch and the program is rejected.
#
# The old `fail` guard accepted this: it contributed the null environment,
# which was the identity for environment intersection. The `fail` construct
# contributes only the binding for its subject, which is stricter.

interface Test { Foo(), Bar() }
interface Other { Ping() }

def bad(x: Test?, y: Other?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x); free(y)
        receive Bar() from x -> (fail(x): Unit)
    }
}

def main(): Unit {
    let m = new[Test] in
    let o = new[Other] in
    m ! Foo();
    bad(m, o)
}

main()
