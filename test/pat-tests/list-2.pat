def snoc(xs : List(Int), x : Int): List(Int) {
<<<<<<< HEAD
    caseL xs : List(Int) of {
=======
    case xs : List(Int) of {
>>>>>>> 904c4ea6bba0191dca3f424e9f7d1f0bb027dccc
        nil -> (x :: (nil : List(Int)))
      | (y :: ys) -> (y :: snoc(ys, x))
    }
}

def reverse(xs : List(Int)): List(Int) {
<<<<<<< HEAD
    caseL xs : List(Int) of {
          nil -> nil
=======
    case xs : List(Int) of {
          nil -> (nil : List(Int))
>>>>>>> 904c4ea6bba0191dca3f424e9f7d1f0bb027dccc
        | (y :: ys) -> snoc(reverse(ys), y)
    }
}

def main(): Unit {
    let xs = (1 :: (2 :: (3 :: (nil : List(Int))))) in
<<<<<<< HEAD
    caseL reverse(xs) : List(Int) of {
=======
    case reverse(xs) : List(Int) of {
>>>>>>> 904c4ea6bba0191dca3f424e9f7d1f0bb027dccc
        nil -> print("nil")
      | (y :: ys) -> print(intToString(y))
  }
}

main()
