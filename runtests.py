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
import getpass
import calendar
import sqlite3 as db
import time
import re


# Our command-line interface
argp = argparse.ArgumentParser(
    description="Run some Test262-style tests with some JS implementation: by default, with JSRef.")

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
                  default=os.path.join("interp","run_js"), help="Where to find the interpreter.")

argp.add_argument("--interp_version", action="store", metavar="version", default="",
    help="The version of the interpreter you're running. Default is the git hash of the current directory.")

argp.add_argument("--webreport",action="store_true",
    help="Produce a web-page of your results in the default web directory. Requires pystache.")

argp.add_argument("--templatedir",action="store",metavar="path",
    default=os.path.join(os.pardir,os.pardir,os.pardir,"web","test_results"),
    help="Where to find our web-templates when producing reports")

argp.add_argument("--reportdir",action="store",metavar="path",
    default=os.path.join(os.pardir,os.pardir,os.pardir,"web","test_results"),
    help="Where to put our test reports")

argp.add_argument("--title",action="store",metavar="string", default="",
    help="Optional title for this test. Will be used in the report filename, so no spaces please!")

argp.add_argument("--note",action="store",metavar="string", default="",
    help="Optional explanatory note to be added to the test report.")

argp.add_argument("--noindex",action="store_true",
    help="Don't attempt to build an index.html for the reportdir")

argp.add_argument("--dbsave",action="store_true",
    help="Save the results of this testrun to the database")

argp.add_argument("--dbpath",action="store",metavar="path",
    default="test_data/test_results.db",
    help="Path to the database to save results in. The default should usually be fine. Please don't mess with this unless you know what you're doing.")

argp.add_argument("--verbose",action="store_true",
    help="Print the output of the tests as they happen.")

argp.add_argument("--debug",action="store_true",
    help="Run the interpreter with debugging flags (-print-heap -verbose -skip-init)")

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

    testname = ""
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
        self.testname = os.path.basename(filename)
        self.result = result
        self.stdout = stdout
        self.stderr = stderr

        # If this was a sputnik test, it may have expected to fail.
        # If so, we will need to invert the return value later on.
        with open(filename) as f:
            # Report the result of this test
            self.negative = "@negative" in f.read()

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

    def report_dict(self):
        return {"testname":self.testname,
                "filename":self.filename,
                "stdout":self.stdout,
                "stderr":self.stderr}

class DBManager:
    PASS = "PASS"
    FAIL = "FAIL"
    ABORT = "ABORT"

    con = None
    curdir = os.getcwd()

    def __init__(self):
        if not os.path.isfile(args.dbpath):
            print args.dbpath
            print """ You need to set up your personal results database before saving data to it.
            See the README for details. """
            exit(1)
        self.con = db.connect(args.dbpath)

    def makerelative(self,path):
        return re.sub("^"+self.curdir+"/","",path)

    def report_results(self,results):
        test_pipe = subprocess.Popen(["git","rev-parse","HEAD"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        githash,errors = test_pipe.communicate()
        version = re.sub(r'\n','',githash)
        if args.interp_version:
            version = args.interp_version
        with self.con:
            cur = self.con.cursor()
            cur.execute("insert into test_batch_runs(time, implementation, impl_path, impl_version, title, notes, timestamp, system, osnodename, osrelease, osversion, hardware) values (?,?,?,?,?,?,?,?,?,?,?,?)",
                        (results["timetaken"],
                         results["implementation"],
                         args.interp_path,
                         version,
                         results["testtitle"],
                         results["testnote"],
                         calendar.timegm(time.gmtime()),
                         results["system"],
                         results["osnodename"],
                         results["osrelease"],
                         results["osversion"],
                         results["hardware"]))
            cur.execute("SELECT id FROM test_batch_runs ORDER BY id DESC LIMIT 1")
            batchid = cur.fetchone()[0]
            insert_single_stmt = "insert into single_test_runs(test_id, batch_id, status, stdout, stderr) values (?,?,?,?,?)"
            def insert_single(status,case):
                cur.execute(insert_single_stmt,
                            (self.makerelative(case["filename"]),
                             batchid,
                             status,
                             case["stdout"],
                             case["stderr"]))
            for case in results["aborts"]:
                # Insert abort cases
                insert_single(self.ABORT,case)
            for case in results["failures"]:
                # Insert fail cases
                insert_single(self.FAIL,case)
            for case in results["passes"]:
                # Insert pass cases
                insert_single(self.PASS,case)
            self.con.commit()


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
    aborted_tests = []

    # How long did it take? In seconds. Set by whoever actually does the running.
    time_taken = 0

    # Possibly a database to save our results to
    dbmanager = None

    def __init__(self):
        if(args.dbsave):
            self.dbmanager = DBManager()

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
            self.aborted_tests.append(result)
        else:
              print "Something really weird happened"
              exit(1)
        if args.verbose or args.debug:
            print result.stdout
            print result.stderr

    def start_test(self,filename):
        self.print_heading(filename)
        return lambda code,stdout,stderr: self.__record_results__(TestResult(filename,code,stdout,stderr))

    def make_report(self):
        (sysname, nodename, release, version, machine) = os.uname()

        return {"testtitle":args.title,
                "testnote":args.note,
                "implementation":self.impl_name(),
                "system":sysname,
                "timetaken":self.time_taken,
                "osnodename":nodename,
                "osrelease":release,
                "osversion":version,
                "hardware":machine,
                "time":time.asctime(time.gmtime()),
                "user":getpass.getuser(),
                "numpasses":len(self.passed_tests),
                "numfails":len(self.failed_tests),
                "numaborts":len(self.aborted_tests),
                "aborts":map(lambda x:x.report_dict() , self.aborted_tests),
                "failures":map(lambda x:x.report_dict() , self.failed_tests),
                "passes":map(lambda x:x.report_dict() , self.passed_tests)}

    def update_database(self):
        self.dbmanager.report_results(self.make_report())

    def impl_name(self):
        if args.spidermonkey: return "SpiderMonkey"
        if args.nodejs: return "node.js"
        if args.lambdaS5: return "LambdaS5"
        return "JSRef"


    def produce_web_page(self):
        import pystache

        report = self.make_report()

        simplerenderer = pystache.Renderer(escape = lambda u: u)
        with open(os.path.join(args.templatedir,"template.tmpl"),"r") as outer:
            with open(os.path.join(args.templatedir,"test_results.tmpl"),"r") as template:
                outfilenamebits = ["report",getpass.getuser(),self.impl_name()]
                if args.title : outfilenamebits.append(args.title)
                outfilenamebits.extend([time.strftime("%Y-%m-%dT%H%M%SZ",time.gmtime())])
                outfilename = "-".join(outfilenamebits)+".html"
                with open(os.path.join(args.reportdir,outfilename),"w") as outfile:
                    outfile.write(simplerenderer.render(outer.read(),{"body":pystache.render(template.read(),report)}))

        if not args.noindex: self.index_reports()

    def index_reports(self):
        import pystache
        import urllib
        # Get a list of all non-index html files in the reportdir
        filenames = filter(lambda x:x!="index.html",filter(lambda x:x.endswith(".html"),os.listdir(args.reportdir)))
        filenames.sort()
        filenames = map(lambda x:{"linkname":os.path.basename(x),"filename":urllib.quote(os.path.basename(x))},filenames)
        simplerenderer = pystache.Renderer(escape = lambda u: u)
        with open(os.path.join(args.templatedir,"template.tmpl"),"r") as outer:
            with open(os.path.join(args.templatedir,"index.tmpl"),"r") as template:
                with open(os.path.join(args.reportdir,"index.html"),"w") as outfile:
                    outfile.write(simplerenderer.render(outer.read(),{"body":pystache.render(template.read(),{"testlist":filenames})}))


    def end_message(self):
        if len(self.failed_tests)>0:
            print "The following tests failed:"
            for failure in self.failed_tests:
                print failure.filename
        if len(self.aborted_tests)>0:
            print "The following tests were abandoned"
            for abandoned in self.aborted_tests:
                print abandoned.filename
        print "There were "+str(len(self.passed_tests))+" passes, "+str(len(self.failed_tests))+"  fails, and "+str(len(self.aborted_tests))+" abandoned."
        if args.webreport:
            self.produce_web_page()
        if args.dbsave:
            self.update_database()

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

# Does this test try to load other libraries?
def usesInclude(filename):
    with open(filename) as f:
        return "$INCLUDE" in f.read()

def jsRefArgBuilder(filename):
    # Normally we run a test like this:
    #./interp/run_js -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js -file filename
    # But if this is a LambdaS5 test, we need additional kit, like this:
    # ./interp/run_js -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js -test_prelude tests/LambdaS5/lambda-pre.js -test_prelude filename -file tests/LambdaS5/lambda-post.js
    # We can tell if it's a LambdaS5 test, because those start with "tests/LambdaS5/unit-tests/".
    # In addition, we may want to add some debug flags.
    arglist = [args.interp_path,
               "-jsparser",
               os.path.join("interp","parser","lib","js_parser.jar")]
    if args.debug:
        arglist.append("-print-heap")
        arglist.append("-verbose")
        arglist.append("-skip-init")
    arglist.append("-test_prelude")
    arglist.append(os.path.join("interp","test_prelude.js"))
    if filename.startswith(os.path.join(os.getcwd(),"tests/LambdaS5/unit-tests/")):
        arglist.append("-test_prelude")
        arglist.append("tests/LambdaS5/lambda-pre.js")
        arglist.append("-test_prelude")
        arglist.append(filename)
        arglist.append("-file")
        arglist.append("tests/LambdaS5/lambda-post.js")
    elif filename.startswith(os.path.join(os.getcwd(), "tests/SpiderMonkey/")):
        arglist.append("-test_prelude")
        arglist.append("interp/test_prelude_SpiderMonkey.js")
        arglist.append("-test_prelude")
        arglist.append("tests/SpiderMonkey/tests/shell.js")
        arglist.append("-file")
        arglist.append(filename)
    elif usesInclude(filename):
        if args.verbose or args.debug:
            print "Using include libs."
        arglist.append("-test_prelude")
        arglist.append("interp/libloader.js")
        arglist.append("-file")
        arglist.append(filename)
    else:
        arglist.append("-file")
        arglist.append(filename)
    return arglist

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
    test_runner = jsRefArgBuilder

# Now let's get down to the business of running the tests
starttime = calendar.timegm(time.gmtime())
for filename in args.filenames:
    filename = os.path.abspath(filename)
    current_test = printer.start_test(filename)

    setup()
    test_pipe = subprocess.Popen(test_runner(filename), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output,errors = test_pipe.communicate()
    output = output.decode("utf8").encode("ascii","xmlcharrefreplace")
    errors = errors.decode("utf8").encode("ascii","xmlcharrefreplace")
    ret = test_pipe.returncode
    teardown()

    current_test(ret,output,errors)

printer.time_taken = calendar.timegm(time.gmtime()) - starttime
printer.end_message()
