interface Test { }

def ignore(x: Test!1): Unit { () }

def main(): Unit {
    let f = fun(x: Test!1): Unit {
        print("Ignoring!"); ignore(x); print("Ignored!")
    } in
    let mb = new[Test] in
    f(mb);
    free(mb);
    print("Freed!")
}

main()
