interface Worker { Start(Done!) }
interface Done { Ack() }

def worker(self: Worker?): Unit {
    guard self : Start {
        receive Start(done) from self1 ->
            done ! Ack();
            free(self1)
    }
}

def main(): Unit {
    let done = new[Done] in
    let worker_mb = new[Worker] in
    spawn { worker(worker_mb) };
    worker_mb ! Start(done);
    guard done : Ack {
        receive Ack() from done1 ->
            free(done1);
            print("done")
    }
}

main()