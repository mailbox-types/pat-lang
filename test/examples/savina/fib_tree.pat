data FibTask = FibBase | FibStep (FibTask) (FibTask)

interface FibMb {
    Req(FibMb!, FibTask),
    Resp(Int)
}

## build FibTask tree for fib(n) without spawning actors
def buildTask(n: Int): FibTask {
    if (n <= 2) {
        FibBase
    } else {
        FibStep(buildTask(n - 1), buildTask(n - 2))
    }
}

## evaluate FibTask tree concurrently:
## FibBase contributes 1; FibStep spawns two actors for
## subtasks, collects results, and returns the sum
def fib(self: FibMb?): Unit {
    guard self: Req {
        receive Req(replyTo, task) from self ->
            case task of {
                FibBase ->
                    replyTo ! Resp(1);
                    free(self)
              | FibStep(leftTask, rightTask) ->
                    let fib1Mb = new [FibMb] in
                    spawn { fib(fib1Mb) };
                    let fib2Mb = new [FibMb] in
                    spawn { fib(fib2Mb) };
                    fib1Mb ! Req(self, leftTask);
                    fib2Mb ! Req(self, rightTask);
                    guard self: Resp . Resp {
                        receive Resp(r1) from self ->
                            guard self: Resp {
                                receive Resp(r2) from self ->
                                    free(self);
                                    replyTo ! Resp(r1 + r2)
                            }
                    }
            }
    }
}

## Launcher.
def main(): Unit {
    let task = buildTask(5) in
    let fibMb = new [FibMb] in
    spawn { fib(fibMb) };
    let self = new [FibMb] in
    fibMb ! Req(self, task);
    guard self: Resp {
        receive Resp(f) from self ->
            free(self);
            print(concat("Result: ", intToString(f)))
    }
}

main()

