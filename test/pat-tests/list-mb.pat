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
    let mbs = spawnMbs(nil) in
    test(mbs);
    print("done")
}

main()
