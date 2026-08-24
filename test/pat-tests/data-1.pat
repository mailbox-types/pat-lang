##   - nullary constructor (Nothing) — no fields
##   - unary constructor (Just a) — one type-parameter field
##   - pattern matching on user-defined type
##   - annotation required for bare nullary constructor
##       (Nothing : Maybe(Int)) so checker knows which type intended

data Maybe a = Nothing | Just a

def fromMaybe(x: Maybe(Int), default: Int): Int {
    case x of {
        Nothing -> default
      | Just(v) -> v
    }
}

def main(): Unit {
    let x = Just(42) in
    let y = (Nothing : Maybe(Int)) in
    print(intToString(fromMaybe(x, 0)));   ## should print 42
    print(intToString(fromMaybe(y, 0)))    ## should print 0
}

main()

