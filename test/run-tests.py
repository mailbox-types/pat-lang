#!/usr/bin/env python3
import sys
import json
import subprocess

# Assumes the file is run from the tests directory, and that the executable
# is located at "../mbcheck"

def error(msg):
    print(msg, file=sys.stderr)
    sys.exit(-1)

def run_tests(testsuite):
    overall_result = True
    executable = "../mbcheck"

    def normalise_output(output):
        return output.replace("\r\n", "\n")

    # Runs a test group, checking the exit code
    def run_group(group):
        nonlocal overall_result
        print("===", "Group:", group["group"], "===")
        for test in group["tests"]:
            command = [executable] + test.get("args", []) + [test["filename"]]
            process_result = subprocess.run(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            result = True
            stdout = normalise_output(process_result.stdout)
            stderr = normalise_output(process_result.stderr)

            if "exit_code" in test:
                result = (result and process_result.returncode == test["exit_code"])
            if "stdout" in test:
                result = (result and stdout == test["stdout"])
            if "stderr" in test:
                result = (result and stderr == test["stderr"])

            result_str = "PASS" if result else "FAIL"
            print(f"{test['name']}: ({result_str})")
            if not result:
                overall_result = False
                print("  Command:", " ".join(command))
                print("  Exit code:", process_result.returncode)
                if "exit_code" in test:
                    print("  Expected exit code:", test["exit_code"])
                if "stdout" in test:
                    print("  Expected stdout:", repr(test["stdout"]))
                    print("  Actual stdout:  ", repr(stdout))
                if "stderr" in test:
                    print("  Expected stderr:", repr(test["stderr"]))
                    print("  Actual stderr:  ", repr(stderr))

    if "groups" in testsuite:
        for group in testsuite["groups"]:
            run_group(group)
    else:
        error("Malformed testsuite: expected 'groups'")

    return overall_result


def main():
    # Default test suite is tests.json
    test_suite = "tests.json"
    # Can optionally be given as a command-line argument
    if len(sys.argv) > 1:
        test_suite = sys.argv[1]

    # Open and parse test suite, then run
    with open(test_suite, 'r') as testsuite:
        parsed = json.loads(testsuite.read())
        overall_result = run_tests(parsed)
        sys.exit(0 if overall_result else 1)

if __name__ == "__main__":
    main()
