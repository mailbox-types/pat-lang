def main(): Unit {
    let x = (Inl(5) : Sum(Int, Bool)) in
    case x : Sum(Int, Bool) of {
          Inl(x) -> print(intToString(x))
        | Inr(y) -> print("right branch")
    }
}

main()
