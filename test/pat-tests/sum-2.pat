def main(): Unit {
    let x : (Int + Bool) = inl(5) in
    case x of {
          inl(x) -> print(intToString(x))
        | inr(y) -> print("right branch")
    }
}

main()
