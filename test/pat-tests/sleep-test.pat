def sleeperLoop(n: Int, count: Int, delay: Int): Unit {
    if (count <= 0) {
        ()
    } else {
        print(intToString(n));
        print("Sleeping");
        sleep(delay);
        sleeperLoop(n, count - 1, delay)
    }
}

def main(): Unit {
    spawn { sleeperLoop(1, 5, 200) };
    spawn { sleeperLoop(2, 5, 100) }
}

main()
