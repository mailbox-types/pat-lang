# `fail` checks at any type, so it has no type of its own to synthesise.
# Guard bodies are now checked against the expected type, so a bare `fail`
# is fine there (see pat-tests/fail-unannotated-guard.pat); a genuine
# synthesis position such as the right-hand side of a `let` still needs an
# annotation.

interface Test { Foo(), Bar() }

def bad(x: Test?): Unit {
    guard x : Foo {
        receive Foo() from x -> free(x)
        receive Bar() from x -> let y = fail(x) in print(intToString(y))
    }
}

def main(): Unit {
    let m = new[Test] in
    m ! Foo();
    bad(m)
}

main()
