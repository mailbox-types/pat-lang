def foo(): Atom {
    :hello
}

def main(): Unit {
    let x = foo() in
    print("hello")
}

main()
