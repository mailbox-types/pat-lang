interface Test { }

def ignore(x: Test!1): Unit { () }

def main(): Unit {
    let f = fun(x: Test!1): Unit {
        print("Ignoring 1!"); ignore(x); print("Ignored 1!");
        print("Ignoring 2!"); ignore(x); print("Ignored 2!")
    } in
    let mb = new[Test] in
    f(mb);
    free(mb);
    print("Freed!")
}

main()
