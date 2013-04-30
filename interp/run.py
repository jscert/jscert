#!/usr/bin/env python
import argparse
import signal
import subprocess
import os

# A gadget for printing pretty colours for us
class colour_handler:
    NORMAL = "\033[00m"
    HEADING = "\033[35m"
    PASS = "\033[32m"
    FAIL = "\033[31m"
    ABANDON = "\033[33m"

    def print_heading(self,s):
        print self.HEADING+s+self.NORMAL
    def print_pass(self,s):
        print self.PASS+s+self.NORMAL
    def print_fail(self,s):
        print self.FAIL+s+self.NORMAL
    def print_abandon(self,s):
        print self.ABANDON+s+self.NORMAL

colours = colour_handler()

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

if args.spidermonkey:
    print "Warning: SpiderMonkey support is still experimental"
    test_runner = lambda filename : [args.interp_path, filename]
elif args.lambdaS5:
    print "Warning: LambdaS5 support is still experimental"
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
    colours.print_heading(filename)
    filename = os.path.abspath(filename)

    setup()
    ret = subprocess.call(test_runner(filename))
    teardown()

    passed = ret

    # If this was a sputnik test, it may have expected to fail.
    # If so, we invert the return value.
    with open(filename) as f:
        if "@negative" in f.read():
            if ret==0 :
                passed = 1
            elif ret==1 :
                passed = 0

    # Report the result of this test, and collate the results.
    if passed==0:
        colours.print_pass("Passed!")
        passed_tests.append(filename)
    elif passed==1:
        colours.print_fail("Failed :/")
        failed_tests.append(filename)
    else:
        colours.print_abandon("Abandoned...")
        abandoned_tests.append(filename)

print "There were "+len(passed_tests)+" passes, "+len(failed_tests)+"  fails, and "+len(abandoned_tests)+" abandoned."
