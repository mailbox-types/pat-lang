def main(): Unit {
    let x = (Inl(5) : Sum(Int, Bool)) in
    case x of {
          Inl(x) -> print(intToString(x))
        | Inr(y) -> print("right branch")
    }
}

main()
