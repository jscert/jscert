#!/usr/bin/env python
import argparse
import signal
import subprocess

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

argp.add_argument("-i","--init", "-init", dest='init', action='store_true',
                  help='Initialise a test run')

argp.add_argument(
    "-m","--makefile", "-makefile", dest='makefile', action='store_true',
    help="If you Control-C, should I print the list of failed tests?")

argp.add_argument("filename", metavar="filename",
                  help="The test file we want to run.")

args = argp.parse_args()

# The file where test failure messages will be reported to
error_file="/tmp/JsCert_run_tests.tmp"

# What to do if the user hits control-C
def end_message(signal,frame):
    with open(error_file) as f:
        all_failed_tests = f.read()
        if all_failed_tests != "":
            print "Failed tests:"
            print all_failed_tests

if args.makefile:
    signal.signal(signal.SIGINT, end_message)

# Now let's get down to the business of running a test
colours.print_heading(args.filename)

ret = subprocess.call(["interp/run_js",
                       "-jsparser","interp/parser/lib/js_parser.jar",
                       "-test_prelude","interp/test_prelude.js",
                       "-file",args.filename])

passed = ret

# If this was a sputnik test, it may have expected to fail. Invert return value.
with open(args.filename) as f:
    if "@negative" in f.read():
        if ret==0 :
            passed = 1
        elif ret==1 :
            passed = 0

# Report the result of this test, and collate failures in the file.
if passed==0:
    colours.print_pass("Passed!")
elif passed==1:
    colours.print_fail("Failed :/")
    with open(error_file,"a") as f:
        f.write(args.filename+"\n")
else:
    colours.print_abandon("Abandoned...")
