## multiple data declarations and nested use

data Pair a b = MkPair a b
data NonEmpty a = Singleton a | ConsNE a (NonEmpty a)

def headInt(xs: NonEmpty(Int)): Int {
    case xs : NonEmpty(Int) of {
        Singleton(x) -> x
      | ConsNE(x, rest) -> x
    }
}

def headBool(xs: NonEmpty(Bool)): Bool {
    case xs : NonEmpty(Bool) of {
        Singleton(x) -> x
      | ConsNE(x, rest) -> x
    }
}

def main(): Unit {
    let xs = ConsNE(1, Singleton(2)) in
    let ys = Singleton(true) in
    let p = MkPair(headInt(xs), headBool(ys)) in
    case p : Pair(Int, Bool) of {
        MkPair(n, b) -> print(intToString(n))
    }
}

main()

