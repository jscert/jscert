#!/usr/bin/env python
"""
A mini test harness. Runs all the files you specify through an interpreter
you specify, and collates the exit codes for you. Call with the -h switch to
find out about options.
"""

import argparse
import signal
import subprocess
import os

# Some pretty colours for our output messages.
NORMAL = "\033[00m"
HEADING = "\033[35m"
PASS = "\033[32m"
FAIL = "\033[31m"
ABANDON = "\033[33m"

def print_heading(s):
    print HEADING+s+NORMAL
def print_pass(s):
    print PASS+s+NORMAL
def print_fail(s):
    print FAIL+s+NORMAL
def print_abandon(s):
    print ABANDON+s+NORMAL

# Our command-line interface
argp = argparse.ArgumentParser(
    description="Run some Test262-style tests with some JS implementation")

argp.add_argument("filenames", metavar="filename", nargs="+",
                  help="The test file we want to run.")

engines_grp = argp.add_mutually_exclusive_group()

engines_grp.add_argument("--spidermonkey", action="store_true",
    help="Test SpiderMonkey instead of JSRef. If you use this, you should probably also use --interp_path")

engines_grp.add_argument("--lambdaS5", action="store_true",
    help="Test LambdaS5 instead of JSRef. If you use this, you should probably also use --interp_path")

engines_grp.add_argument("--nodejs", action="store_true",
    help="Test node.js instead of JSRef. If you use this, you should probably also use --interp_path")

argp.add_argument("--interp_path", action="store", metavar="path",
                  default="interp/run_js", help="Where to find the interpreter.")

args = argp.parse_args()

# Which tests passed, and which failed?
passed_tests = []
failed_tests = []
abandoned_tests = []

# What to do if the user hits control-C
def end_message(signal,frame):
    print "Interrupted..."
    if len(failed_tests)>0:
        print "The following tests failed:"
        for failure in failed_tests:
            print failure
    if len(abandoned_tests)>0:
        print "The following tests were abandoned"
        for abandoned in abandoned_tests:
            print abandoned
    exit(1)

signal.signal(signal.SIGINT, end_message)

# How should we run this test? With what?
# By default, we do no setup or teardown, and the test runner is a plaintive echo.
setup = lambda : 0
teardown = lambda : 0
test_runner = lambda filename : ['echo "Something weird is happening!"']

# By default, we expect a pass to exit with code 0, and a fail to exit with code 1.
pass_code = 0
fail_code = 1

if args.spidermonkey:
    fail_code = 3 # SpiderMonkey fails on 3.
    test_runner = lambda filename : [args.interp_path, filename]
elif args.nodejs:
    test_runner = lambda filename : [args.interp_path, filename]
elif args.lambdaS5:
    current_dir = os.getcwd()
    setup = lambda : os.chdir(os.path.dirname(args.interp_path))
    teardown = lambda : os.chdir(current_dir)
    test_runner = lambda filename: [os.path.abspath(args.interp_path),
                                    filename]
else:
    test_runner = lambda filename : [args.interp_path,
                                     "-jsparser",
                                     "interp/parser/lib/js_parser.jar",
                                     "-test_prelude","interp/test_prelude.js",
                                     "-file",filename]

# Now let's get down to the business of running the tests
for filename in args.filenames:
    print_heading(filename)
    filename = os.path.abspath(filename)

    setup()
    ret = subprocess.call(test_runner(filename))
    teardown()

    passed = ret

    # If this was a sputnik test, it may have expected to fail.
    # If so, we invert the return value.
    with open(filename) as f:
        if "@negative" in f.read():
            if ret==pass_code :
                passed = fail_code
            elif ret==fail_code :
                passed = pass_code

    # Report the result of this test, and collate the results.
    if passed==pass_code:
        print_pass("Passed!")
        passed_tests.append(filename)
    elif passed==fail_code:
        print_fail("Failed :/")
        failed_tests.append(filename)
    else:
        # JSRef uses a third code for when something really odd happened.
        print_abandon("Abandoned...")
        abandoned_tests.append(filename)

print "There were "+str(len(passed_tests))+" passes, "+str(len(failed_tests))+"  fails, and "+str(len(abandoned_tests))+" abandoned."
