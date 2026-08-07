interface Test { }

def main(): Unit {
    let f = fun(x: Test?): Test? { print("Returning x!"); x } in
    free(f(new[Test]));
    print("Freed!")
}

main()
