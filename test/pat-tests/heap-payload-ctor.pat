### Regression test: a heap value built *inline as a message payload*.
###
### Same underlying issue as heap-arg-ctor.pat, but on the send path: payloads
### are stored in the mailbox and rebound at the receive, so a constructor built
### directly in the send reached the receiver untracked and could not be cased.

data Box a = MkBox a

interface Mb { Msg(Box(Int)) }

def main(): Unit {
    let mb = new[Mb] in
    mb ! Msg(MkBox(42));
    guard mb : Msg {
        receive Msg(b) from mb ->
            free(mb);
            case b of {
                MkBox(n) -> print(intToString(n))
            }
    }
}
main()
