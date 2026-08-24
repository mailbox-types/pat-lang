##   - String as constructor field (fixed binder source)
##   - mixing base types and type parameters in same constructor
##   - 0-parameter (IntTree) vs parameterised (Labeled a)

data Labeled a = Label String a | Unlabeled a
data IntTree   = ILeaf Int | INode IntTree IntTree

def sumTree(t: IntTree): Int {
    case t of {
        ILeaf(n)    -> n
      | INode(l, r) -> sumTree(l) + sumTree(r)
    }
}

def getLabel(x: Labeled(Int)): String {
    case x of {
        Label(s, n) -> s
      | Unlabeled(n) -> "404: Label not found"
    }
}

def main(): Unit {
    ## Tree: INode(INode(ILeaf(1), ILeaf(2)), ILeaf(3))  =>  sum = 6
    let t = INode(INode(ILeaf(1), ILeaf(2)), ILeaf(3)) in
    print(intToString(sumTree(t)));   ## should print 6
    let x = Label("Hello!", 42) in
    print(getLabel(x))                ## should print "Hello!"
}

main()

