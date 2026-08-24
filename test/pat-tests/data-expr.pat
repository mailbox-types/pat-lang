##   - base-type fields: Val carries Int (concrete type, not type parameter)
##   - 0-parameter recursive type: Expr takes no type arguments
##   - Add and Mult carry two Expr subtrees
##   - simple interpreter using structural recursion

data Expr = Val Int | Add Expr Expr | Mult Expr Expr

def eval(e: Expr): Int {
    case e of {
        Val(n)      -> n
      | Add(a, b)  -> eval(a) + eval(b)
      | Mult(a, b) -> eval(a) * eval(b)
    }
}

def main(): Unit {
    ## represents expression tree for (2 + 3) * 4:
    ##
    ##        Mult
    ##       /    \
    ##     Add    Val(4)
    ##    /   \
    ## Val(2) Val(3)

    let e = Mult(Add(Val(2), Val(3)), Val(4)) in
    print(intToString(eval(e)))   ## should print 20
}

main()

