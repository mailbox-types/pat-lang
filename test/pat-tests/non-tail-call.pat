def tcSum(n: Int): Int {
    if (n == 0) {
        0
    } else {
        n + tcSum(n - 1)
    }
}

print(intToString(tcSum(999999)))
