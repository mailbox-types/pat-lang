def printIntList(lst: List(Int)): Unit {
    case lst of {
        | nil -> ()
        | (x :: xs) -> print(intToString(x)); printIntList(xs)
    }
}

def main() : Unit {
    let xs = [1, let x = 2 in x * x, 3, 4 * 4, 5] in
    let emptyList = ([] : List(Int)) in
    printIntList(xs);
    printIntList(emptyList)
}

main()
