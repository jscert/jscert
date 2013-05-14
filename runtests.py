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


# Our command-line interface
argp = argparse.ArgumentParser(
    description="Run some Test262-style tests with some JS implementation")

argp.add_argument("filenames", metavar="filename", nargs="*",
                  help="The test file we want to run. If you don't specify, we'll recursively find all .js files under the current directory.")

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

# Some handy data structures

class TestResult:
    """
    A test result knows what file it came from, whether it passed, failed or
    aborted, and what output it generated along the way.
    """

    # By default, we expect a pass to exit with code 0,
    # and a fail to exit with code 1.
    pass_code = 0
    fail_code = 1

    filename = ""
    result = 0
    stdout = ""
    stderr = ""
    negative = False

    def __init__(self,filename,result,stdout,stderr):
        # Are we testing on SpiderMonkey?
        # That changes the meaning of result codes.
        if args.spidermonkey:
            self.fail_code = 3

        self.filename = filename
        self.result = result
        self.stdout = stdout
        self.stderr = stderr

        # If this was a sputnik test, it may have expected to fail.
        # If so, we will need to invert the return value later on.
        with open(filename) as f:
            # Report the result of this test
            negative = "@negative" in f.read()

    def passed(self):
        if(self.negative):
            return self.result==self.fail_code
        else:
            return self.result==self.pass_code
    def failed(self):
        if(self.negative):
            return self.result==self.pass_code
        else:
            return self.result==self.fail_code
    def aborted(self):
        return not (self.passed() or self.failed())

class ResultPrinter:

    """
    This class maintains the results of our test run, and provides methods to
    report those results, on the command line or on the web.

    """
    # Some pretty colours for our output messages.
    NORMAL = "\033[00m"
    HEADING = "\033[35m"
    PASS = "\033[32m"
    FAIL = "\033[31m"
    ABANDON = "\033[33m"

    # Which tests passed, and which failed?
    passed_tests = []
    failed_tests = []
    abandoned_tests = []

    def print_heading(self,s):
        print self.HEADING+s+self.NORMAL
    def print_pass(self,s):
        print self.PASS+s+self.NORMAL
    def print_fail(self,s):
        print self.FAIL+s+self.NORMAL
    def print_abandon(self,s):
        print self.ABANDON+s+self.NORMAL

    def __record_results__(self,result):
        if result.passed():
            self.print_pass("Passed!")
            self.passed_tests.append(result)
        elif result.failed():
            self.print_fail("Failed :/")
            self.failed_tests.append(result)
        elif result.aborted():
            self.print_abandon("Aborted...")
            self.abandoned_tests.append(result)
        else:
              print "Something really weird happened"
              exit(1)

    def start_test(self,filename):
        self.print_heading(filename)
        return lambda code,stdout,stderr: self.__record_results__(TestResult(filename,code,stdout,stderr))

    def end_message(self):
        if len(self.failed_tests)>0:
            print "The following tests failed:"
            for failure in self.failed_tests:
                print failure.filename
        if len(self.abandoned_tests)>0:
            print "The following tests were abandoned"
            for abandoned in self.abandoned_tests:
                print abandoned.filename
        print "There were "+str(len(self.passed_tests))+" passes, "+str(len(self.failed_tests))+"  fails, and "+str(len(self.abandoned_tests))+" abandoned."

    def interrupt_handler(self,signal,frame):
        print "Interrupted..."
        self.end_message()
        exit(1)


# If no test files are specified, search for some and use them.
if not args.filenames:
    for r,d,f in os.walk("."):
        for filename in f:
            if filename.endswith(".js"):
                args.filenames.append(os.path.join(r,filename))

printer = ResultPrinter()

# What to do if the user hits control-C
signal.signal(signal.SIGINT, printer.interrupt_handler)

# How should we run this test? With what?
# By default, we do no setup or teardown, and the test runner is a plaintive echo.
setup = lambda : 0
teardown = lambda : 0
test_runner = lambda filename : ['echo "Something weird is happening!"']

if args.spidermonkey:
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
    filename = os.path.abspath(filename)
    current_test = printer.start_test(filename)

    setup()

    test_pipe = subprocess.Popen(test_runner(filename), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output,errors = test_pipe.communicate()
    ret = test_pipe.returncode
    teardown()

    current_test(ret,output,errors)

printer.end_message()
