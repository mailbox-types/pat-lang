#!/usr/bin/env python3
import os
import subprocess

EXAMPLES =\
    [
        # Paper examples
        ("Future", os.path.join("test", "examples", "de_liguoro_padovani", "future.pat")),
        ("Use-after-free 1 (should fail)", os.path.join("test", "errors",  "uaf1.pat")),
        ("Use-after-free 2 (should fail)", os.path.join("test", "errors",  "uaf2.pat")),
        ("Use-after-free 3 (should fail)", os.path.join("test", "errors",  "uaf3.pat")),
        ("Aliasing via communication 1 (should fail)", os.path.join("test",\
                                                                    "errors",\
                                                                    "alias_comm1.pat")),
        ("Aliasing via communication 2 (should fail)", os.path.join("test",\
                                                                    "errors",\
                                                                    "alias_comm2.pat")),
        ("Products", os.path.join("test", "examples", "products.pat")),
        ("Interfaces", os.path.join("test", "examples", "interfaces.pat")),
        ("Robots", os.path.join("test", "examples", "robotsn.pat")),
        # Benchmarks
        ("Lock", os.path.join("test", "examples", "de_liguoro_padovani", "lock.pat")),
        ("Account", os.path.join("test", "examples", "de_liguoro_padovani", "account.pat")),
        ("AccountF", os.path.join("test", "examples", "de_liguoro_padovani", "account_future.pat")),
        ("Master-Worker", os.path.join("test", "examples", "de_liguoro_padovani", "master_worker.pat")),
        ("Session Types", os.path.join("test", "examples", "de_liguoro_padovani", "sessions.pat")),
        ("Ping Pong", os.path.join("test", "examples", "savina", "ping_pong_strict.pat")),
        ("Thread Ring", os.path.join("test", "examples", "savina", "thread_ring.pat")),
        ("Counter", os.path.join("test", "examples", "savina", "count.pat")),
        ("K-Fork", os.path.join("test", "examples", "savina", "kfork.pat")),
        ("Fibonacci", os.path.join("test", "examples", "savina", "fib.pat")),
        ("Big", os.path.join("test", "examples", "savina", "big.pat")),
        ("Philosopher", os.path.join("test", "examples", "savina", "philosopher.pat")),
        ("Smokers", os.path.join("test", "examples", "savina", "cig_smok.pat")),
        ("Log Map", os.path.join("test", "examples", "savina", "log_map.pat")),
        ("Transaction", os.path.join("test", "examples", "savina", "banking.pat"))
    ]

def run_example(name, path):
    print("Checking " + name)
    subprocess.run(["./pat " + path], shell=True)
    print()

def run_examples():
    for (name, path) in EXAMPLES:
        run_example(name, path)

if __name__ == "__main__":
    run_examples()
