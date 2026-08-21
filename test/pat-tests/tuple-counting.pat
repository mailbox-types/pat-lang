### Regression test for reference counting of tuple *construction*.
###
### Building a tuple captures one reference per field, so a field mentioned twice
### needs a dup for the second occurrence. A translation that emitted no dups for
### tuple fields would under-count 'mb' here: the tuple holds two references but
### only one was accounted for, so dropping it took the count below zero.
###
### Needs -q -j: aliasing 'mb' into both fields is only well-typed with
### quasilinearity and disjointness checking relaxed.

interface Test { }

def ignore(x: (Test! * Test!)): Unit {
    ()
}

def main(): Unit {
    let mb = new[Test] in
    spawn { ignore((mb, mb)) };
    guard mb : 1 {
        free -> print("freed")
    }
}
main()
