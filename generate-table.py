#!/usr/bin/env python3
import os
import subprocess
from tabulate import tabulate

REPETITIONS = 1000

BENCHMARKS =\
    [
        ("Lock", os.path.join("test", "examples", "de_liguoro_padovani", "lock.pat")),
        ("Future", os.path.join("test", "examples", "de_liguoro_padovani", "future.pat")),
        ("Account", os.path.join("test", "examples", "de_liguoro_padovani", "account.pat")),
        ("AccountF", os.path.join("test", "examples", "de_liguoro_padovani", "account_future.pat")),
        ("Master-Worker", os.path.join("test", "examples", "de_liguoro_padovani", "master_worker.pat")),
        ("Session Types", os.path.join("test", "examples", "de_liguoro_padovani", "sessions.pat")),
        ("Ping Pong", os.path.join("test", "examples", "savina", "ping_pong_strict.pat")),
        ("Thread Ring", os.path.join("test", "examples", "savina", "thread_ring.pat")),
        ("Counter", os.path.join("test", "examples", "savina", "count.pat")),
        ("K-Fork", os.path.join("test", "examples", "savina", "lists", "kfork.pat")),
        ("Fibonacci", os.path.join("test", "examples", "savina", "fib.pat")),
        ("Big", os.path.join("test", "examples", "savina", "lists", "big.pat")),
        ("Philosopher", os.path.join("test", "examples", "savina", "philosopher.pat")),
        ("Smokers", os.path.join("test", "examples", "savina", "lists", "cig_smok.pat")),
        ("Log Map", os.path.join("test", "examples", "savina", "log_map.pat")),
        ("Transaction", os.path.join("test", "examples", "savina", "lists", "banking.pat")),
	("Barber", os.path.join("test", "examples", "savina", "lists", "barber.pat")),
     ]

# Tries to run in strict mode -- returns True if it works, False otherwise
def try_strict(path):
    return subprocess.run(["./pat", "--mode=strict", path],\
                          capture_output=True).returncode == 0

def run_benchmark(name, path):
    print("Running example " + name)
    is_strict = try_strict(path)
    time = str(subprocess.run(["./pat", "-b", str(REPETITIONS), path],\
                              capture_output=True, text=True).stdout)
    return (name, is_strict, time)

def main():
    print("Generating table -- this may take some time.")
    results = [run_benchmark(name, path) for (name, path) in BENCHMARKS]
    print(tabulate(results, headers=["Name", "Strict", "Time (ms)"], tablefmt='grid'))

if __name__ == "__main__":
    main()
