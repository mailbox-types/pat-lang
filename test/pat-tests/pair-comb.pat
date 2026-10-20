interface I1 { M1() }
interface I2 { M2() }

def sendToBoth(pair: (I1! * I2!)): Unit {
    let (mb1, mb2) = pair in
    mb1 ! M1();
    mb2 ! M2()
}

def receiveAndFree(pair: (I1? * I2?)): Unit {
    let (mb1, mb2) = pair in
    guard mb1 : M1 {
        receive M1() from mb1 -> free(mb1)
    };
    guard mb2 : M2 {
        receive M2() from mb2 -> free(mb2)
    }
}

def main(): Unit {
    let mb1 = new[I1] in
    let mb2 = new[I2] in
    let pair = (mb1, mb2) in
    spawn { sendToBoth(pair) };
    receiveAndFree(pair)
}

main()
