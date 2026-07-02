interface Self { Msg(Other!) }
interface Other { Reply() }

def interprocess(self: Self?, other1: Other!): Unit {
    guard self : Msg {
        receive* Msg(other2) from self ->
            other1 ! Reply();
            free(self)
    }
}

def main(): Unit {
    let self = new[Self] in
    let other = new[Other] in
    spawn { interprocess(self, other) };
    self ! Msg(other);
    guard other : Reply {
        receive Reply() from other ->
            free(other);
            print("done")
    }
}

main()
