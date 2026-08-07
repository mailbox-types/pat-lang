interface Test { }

def main(): Unit {
    let mb = new[Test] in
    let sum : (Test!1 + Unit) = inl(mb) in
    guard mb : 1 {
        free -> ()
    };
    case sum of {
        inl(x): Test!1 -> ()
        | inr(y): Unit -> ()
    }
}

main()
