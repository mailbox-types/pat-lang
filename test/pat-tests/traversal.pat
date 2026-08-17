data Tree a = Leaf a | Node (Tree a) (Tree a)

def append(xs : List(Int), ys : List(Int)) : List(Int) {
  case xs : List(Int) of {
      nil -> ys
    | (z :: zs) -> (z :: append(zs, ys))
  }
}

def traverse(t : Tree(Int)) : List(Int) {
  case t : Tree(Int) of {
      Leaf(v)   -> (v :: (nil : List(Int)))
    | Node(l,r) -> append(traverse(l), traverse(r))
  }
}

def main() : Unit {
    let t = Node(Node(Leaf(3), Leaf(1)), Node(Leaf(4), Leaf(1))) in
    let xs = traverse(t) in
    case xs : List(Int) of {
      nil -> print("Impossible!")
      | (y :: ys) -> print(intToString(y))
    }
}

main()

