def snoc(xs : List(Int), x : Int): List(Int) {
    caseL xs : List(Int) of {
        nil -> (x :: (nil : List(Int)))
      | (y :: ys) -> (y :: snoc(ys, x))
    }
}

def reverse(xs : List(Int)): List(Int) {
    caseL xs : List(Int) of {
          nil -> nil
        | (y :: ys) -> snoc(reverse(ys), y)
    }
}

def main(): Unit {
    let xs = (1 :: (2 :: (3 :: (nil : List(Int))))) in
    caseL reverse(xs) : List(Int) of {
        nil -> print("nil")
      | (y :: ys) -> print(intToString(y))
  }
}

main()
