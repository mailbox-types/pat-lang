def main() : Unit {
    let xs = (5 :: (nil : List(Int))) in
    case xs : List(Int) of {
          nil -> print("nil")
        | (y :: ys) -> print(intToString(y))
    }
}

main()
