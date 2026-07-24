interface Test { Msg() }

def main(): Unit {
    let mb = new[Test] in
    spawn {
        let f = (linfun(): Unit { mb ! Msg() }) in
        if (true) {
            f()
        } else {
            f()
        }
    };
    guard mb : Msg {
        free -> ()
        receive Msg() from mb ->
            print("Done");
            free(mb)
    }
}
main()
