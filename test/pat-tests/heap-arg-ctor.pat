### Regression test: a heap value built *inline as a call argument*.
###
### Constructors, tuples and lambdas are reference-counted via a tracked
### allocation, which previously only happened for let-bound values. An argument
### built at the call site (rather than let-bound first) reached the callee as an
### untracked value, so destructuring it failed with
### "Non runtime-name in runtime_name_of_var".
###
### Nested on purpose: the mailbox sits inside a constructor inside a tuple.

data Either a b = Left a | Right b

interface Mb {
    Done()
}

def wrap(y: Either(Mb![R], Int)): Unit {
    let t = (y, 1) in
    let (m, n) = t in
    case m : Either(Mb![R], Int) of {
        Left(mb)  -> mb ! Done()
      | Right(r) -> ()
    }
}

def main(): Unit {
    let mb = new [Mb] in
    spawn { guard mb : Done { free -> () receive Done() from mb -> (print("freed"); free(mb)) } };
    wrap(Left(mb))
}

main()
