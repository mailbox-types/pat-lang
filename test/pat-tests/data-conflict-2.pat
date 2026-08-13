# should fail: Nil already built-in constructor
data MyList a = Nil | MyCons a (MyList a)

def main(): Unit { () }
main()

