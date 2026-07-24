interface Dummy { }
def main(): Unit {
    let mb = new[Dummy] in
    let f = linfun(): Unit { free(mb); print("Freed!") } in
    f()
}
main()
