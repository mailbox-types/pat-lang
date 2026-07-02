def main(): (Bool * Int * String) {
    let (x, y, z) = (1, "hello", true) in
    (z, x, y)
}

def run(): Unit {
    let (b, x, y) = main() in
    print(concat(intToString(x), y))
}

run()
