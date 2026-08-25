## Inferring a `Self` argument's type parameters from its sibling `Param`
## arguments, so that nullary constructors need no annotation in synthesis
## position (i.e. the `Empty` in `let s = Push(1, Empty)`).
##   - Self field to the right of the Param field (the Cons/Nil shape)
##   - Self field to the left of the Param field (order-independence)
##   - two type parameters, each fixed by a different Param field

data Stack a    = Empty  | Push a (Stack a)
data Rev a      = REmpty | RPush (Rev a) a
data Tagged a b = TEmpty | TCons a b (Tagged a b)

def depth(s: Stack(Int)): Int {
    case s of {
        Empty -> 0
      | Push(x, rest) -> 1 + depth(rest)
    }
}

def rdepth(r: Rev(Int)): Int {
    case r of {
        REmpty -> 0
      | RPush(rest, x) -> 1 + rdepth(rest)
    }
}

def tdepth(t: Tagged(Int, String)): Int {
    case t of {
        TEmpty -> 0
      | TCons(a, b, rest) -> 1 + tdepth(rest)
    }
}

def main(): Unit {
    ## Self field on the right, nested
    let s = Push(1, Push(2, Push(3, Empty))) in
    print(intToString(depth(s)));       ## should print 3

    ## Self field on the left, nested
    let r = RPush(RPush(REmpty, 1), 2) in
    print(intToString(rdepth(r)));      ## should print 2

    ## Both type parameters inferred
    let t = TCons(1, "x", TEmpty) in
    print(intToString(tdepth(t)))       ## should print 1
}

main()
