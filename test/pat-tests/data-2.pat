##   - recursive self-reference in constructor field: ConsNE a (NonEmpty a)
##   - two constructors with different arities (1 vs 2 fields)
##   - instantiated as NonEmpty(Int) below

data NonEmpty a = Singleton a | ConsNE a (NonEmpty a)

def length(xs: NonEmpty(Int), acc: Int): Int {
    case xs of {
        Singleton(x) -> acc + 1
      | ConsNE(x, rest) -> length(rest, acc + 1)
    }
}

def main(): Unit {
    ## ConsNE(1, ConsNE(2, Singleton(3))) represents [1, 2, 3]
    let xs = ConsNE(1, ConsNE(2, Singleton(3))) in
    let n = length(xs, 0) in
    print(intToString(n))   ## should print 3
}

main()

