def main(): Unit {
    let x = (inl(5) : (Int + Bool)) in
    case x : (Int + Bool) of {
          inl(x) -> print(intToString(x))
        | inr(y) -> print("right branch")
    }
}

main()
