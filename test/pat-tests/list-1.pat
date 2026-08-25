def main() : Unit {
    let xs = (5 :: nil) in
    case xs of {
          nil -> print("nil")
        | (y :: ys) -> print(intToString(y))
    }
}

main()
