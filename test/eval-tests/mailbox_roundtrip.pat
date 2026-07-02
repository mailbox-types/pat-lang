interface Box { Msg(Int) }

def main(): Unit {
    let mb = new[Box] in
    mb ! Msg(42);
    guard mb : Msg {
        receive Msg(x) from mb1 ->
            free(mb1);
            print(intToString(x))
    }
}

main()