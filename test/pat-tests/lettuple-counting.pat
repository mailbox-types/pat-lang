interface Recv { Response(Int) }

def sender(mb: Recv!): Unit {
    mb ! Response(42)
}

def main(): Int {
    let self = new[Recv] in
    spawn { sender(self) };
    let (x, self) =
        guard self : Response {
            receive Response(x) from self -> (x, self)
        }
    in
    free(self);
    x
}

print(intToString(main()))
