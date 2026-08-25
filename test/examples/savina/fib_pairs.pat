interface FibActor { Request(Int, FibActor!), Response(Int) }

def fibActor(self: FibActor?): Unit {
    # Fib actor will always get a request
    guard self : Request {
        receive Request(n, parent) from self ->
            # Base case: Send 1 to parent
            if (n <= 2) {
                parent ! Response(1);
                free(self)
            # Otherwise: spawn new actors and send requests
            } else {
                let childMB1 = new[FibActor] in
                spawn { fibActor(childMB1) };
                childMB1 ! Request(n - 1, self);

                let childMB2 = new[FibActor] in
                spawn { fibActor(childMB2) };
                childMB2 ! Request(n - 2, self);
                let (x1, self) =
                    guard self : Response.Response {
                        receive Response(x1) from self -> (x1, self)
                    }
                in
                let (x2, self) =
                    guard self : Response {
                        receive Response(x2) from self -> (x2, self)
                    }
                in
                free(self);
                parent ! Response(x1 + x2)
            }
    }
}

def mainFibActor(n: Int): Int {
   let root = new[FibActor] in
    let firstActor = new[FibActor] in
    spawn { fibActor(firstActor) };
    firstActor ! Request(n, root);
    guard root : Response {
        receive Response(x) from root ->
            free(root);
            x
    }
}
print(intToString(mainFibActor(5)))
