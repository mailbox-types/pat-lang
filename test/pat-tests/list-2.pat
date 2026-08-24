def snoc(xs : List(Int), x : Int): List(Int) {
    case xs of {
        nil -> (x :: (nil : List(Int)))
      | (y :: ys) -> (y :: snoc(ys, x))
    }
}

def reverse(xs : List(Int)): List(Int) {
    case xs of {
          nil -> nil
        | (y :: ys) -> snoc(reverse(ys), y)
    }
}

def main(): Unit {
    let xs = (1 :: (2 :: (3 :: (nil : List(Int))))) in
    case reverse(xs) of {
        nil -> print("nil")
      | (y :: ys) -> print(intToString(y))
  }
}

main()
