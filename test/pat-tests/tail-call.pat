def tcSum(n: Int, tot: Int): Int {
    if (n == 0) {
        tot
    } else {
        tcSum(n - 1, n + tot)
    }
}

print(intToString(tcSum(999999, 0)))
