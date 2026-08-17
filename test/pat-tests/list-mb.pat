interface Test {
  Ping()
}

def spawnMbs(acc : List(Test!)) : List(Test!) {
    acc
}

def test(mbs : List(Test!)) : Unit {
    ()
}

def main() : Unit {
    let mbs = spawnMbs(nil : List(Test!)) in
<<<<<<< HEAD
    test(mbs);
    print("done")
}

main()
=======
    test(mbs)
}
>>>>>>> 904c4ea6bba0191dca3f424e9f7d1f0bb027dccc
