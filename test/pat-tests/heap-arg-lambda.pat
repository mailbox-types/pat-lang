### Regression test: a lambda passed *inline as a call argument*, then invoked.
###
### Closures are reference-counted like other heap values. A lambda built at the
### call site arrived in the callee as a raw closure rather than a tracked name,
### so applying it failed with "Function position must be a declaration, lambda,
### or primitive".

def apply(f: (Int) -> Int, v: Int): Int {
    f(v)
}

def main(): Unit {
    print(intToString(apply(fun (x: Int): Int { x + 1 }, 5)))
}
main()
