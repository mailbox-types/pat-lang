interface Test { Msg() }

def producer(consumerRef: Test!): Unit {
    if (randBool()) {
        consumerRef ! Msg();
        producer(consumerRef)
    } else {
        ()
    }
}

def consumer(self: Test?): Unit {
    guard self : Msg* {
        free -> ()
        receive Msg() from self ->
            consumer(self)
    }
}

def main(): Unit {
    let mb = new[Test] in
    spawn { producer(mb) };
    consumer(mb)
}
