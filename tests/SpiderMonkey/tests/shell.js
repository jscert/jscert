/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// Explicitly set the default version.
// See https://bugzilla.mozilla.org/show_bug.cgi?id=522760#c11
if (typeof version != 'undefined')
{
  version(0);
}

var STATUS = "STATUS: ";
var VERBOSE = false;
var SECT_PREFIX = 'Section ';
var SECT_SUFFIX = ' of test - ';
var callStack = new Array();

var gDelayTestDriverEnd = false;

var gTestcases = new Array();
var gTc = gTestcases.length;
var BUGNUMBER = '';
var summary = '';
var description = '';
var expected = '';
var actual = '';
var msg = '';

var SECTION = "";
var VERSION = "";
var BUGNUMBER = "";

/*
 * constant strings
 */
var GLOBAL = "[GLOBAL OBJECT]"
var PASSED = " PASSED! ";
var FAILED = " FAILED! ";

var DEBUG = false;

var DESCRIPTION;
var EXPECTED;

/*
 * Signals to results.py that the current test case should be considered to
 * have passed if it doesn't throw an exception.
 *
 * When the test suite is run in the browser, this function gets overridden by
 * the same-named function in browser.js.
 */
function testPassesUnlessItThrows() {
  print(PASSED);
}

/*
 * wrapper for test case constructor that doesn't require the SECTION
 * argument.
 */

function AddTestCase( description, expect, actual ) {
  new TestCase( SECTION, description, expect, actual );
}

/*
 * Set up test environment.
 *
 */
function startTest() {
  // print out bugnumber

  if ( BUGNUMBER ) {
    print ("BUGNUMBER: " + BUGNUMBER );
  }
}

function TestCase(n, d, e, a)
{
  this.name = n;
  this.description = d;
  this.expect = e;
  this.actual = a;
  this.passed = getTestCaseResult(e, a);
  this.reason = '';
  this.bugnumber = typeof(BUGNUMER) != 'undefined' ? BUGNUMBER : '';
  this.type = (typeof window == 'undefined' ? 'shell' : 'browser');
  gTestcases.push(this);
}

gFailureExpected = false;

TestCase.prototype.dump = function () {
  // let reftest handle error reporting, otherwise
  // output a summary line.
  if (true)
  {
    dump('\njstest: ' + this.path + ' ' +
         'bug: '         + this.bugnumber + ' ' +
         'result: '      + (this.passed ? 'PASSED':'FAILED') + ' ' +
         'type: '        + this.type + ' ' +
         'description: ' + toPrinted(this.description) + ' ' +
//       'expected: '    + toPrinted(this.expect) + ' ' +
//       'actual: '      + toPrinted(this.actual) + ' ' +
         'reason: '      + toPrinted(this.reason) + '\n');
  }
};

TestCase.prototype.testPassed = (function TestCase_testPassed() { return this.passed; });
TestCase.prototype.testFailed = (function TestCase_testFailed() { return !this.passed; });
TestCase.prototype.testDescription = (function TestCase_testDescription() { return this.description + ' ' + this.reason; });

function getTestCases()
{
  return gTestcases;
}

/*
 * The test driver searches for such a phrase in the test output.
 * If such phrase exists, it will set n as the expected exit code.
 */
function expectExitCode(n)
{
  print('--- NOTE: IN THIS TESTCASE, WE EXPECT EXIT CODE ' + n + ' ---');
}

/*
 * Statuses current section of a test
 */
function inSection(x)
{
  return SECT_PREFIX + x + SECT_SUFFIX;
}

/*
 * Report a failure in the 'accepted' manner
 */
function reportFailure (msg)
{
  var funcName = currentFunc();
  var prefix = (funcName) ? "[reported from " + funcName + "] ": "";
  $ERROR(FAILED + prefix + msg);
}

/*
 * Print a non-failure message.
 */
function printStatus (msg)
{
/* js1_6 had...
   msg = String(msg);
   msg = msg.toString();
*/
  msg = msg.toString();
  print (STATUS + msg);
}

/*
 * Print a bugnumber message.
 */
function printBugNumber (num)
{
  BUGNUMBER = num;
  print ('BUGNUMBER: ' + num);
}

function toPrinted(value)
{
  value = String(value);
  return value;
}

function escapeString (str)
{
  $ERROR("escapeString(): Not implemented!");
}

/*
 * assertEq(actual, expected [, message])
 *   Throw if the two arguments are not the same.  The sameness of two values
 *   is determined as follows.  If both values are zero, they are the same iff
 *   their signs are the same.  Otherwise, if both values are NaN, they are the
 *   same.  Otherwise, they are the same if they compare equal using ===.
 * see https://bugzilla.mozilla.org/show_bug.cgi?id=480199 and
 *     https://bugzilla.mozilla.org/show_bug.cgi?id=515285
 */
if (typeof assertEq == 'undefined')
{
  var assertEq =
    function (actual, expected, message)
    {
      function SameValue(v1, v2)
      {
        if (v1 === 0 && v2 === 0)
          return 1 / v1 === 1 / v2;
        if (v1 !== v1 && v2 !== v2)
          return true;
        return v1 === v2;
      }
      if (!SameValue(actual, expected))
      {
        throw new TypeError('Assertion failed: got "' + actual + '", expected "' + expected +
                            (message ? ": " + message : ""));
      }
    };
}

/*
 * Compare expected result to actual result, if they differ (in value and/or
 * type) report a failure.  If description is provided, include it in the
 * failure report.
 */
function reportCompare (expected, actual, description) {
  var expected_t = typeof expected;
  var actual_t = typeof actual;
  var output = "";

  if (typeof description == "undefined")
  {
    description = '';
  }
  else if (VERBOSE)
  {
    printStatus ("Comparing '" + description + "'");
  }

  if (expected_t != actual_t)
  {
    output += "Type mismatch, expected type " + expected_t +
      ", actual type " + actual_t + " ";
  }
  else if (VERBOSE)
  {
    printStatus ("Expected type '" + expected_t + "' matched actual " +
                 "type '" + actual_t + "'");
  }

  if (expected != actual)
  {
    output += "Expected value '" + toPrinted(expected) +
      "', Actual value '" + toPrinted(actual) + "' ";
  }
  else if (VERBOSE)
  {
    printStatus ("Expected value '" + toPrinted(expected) +
                 "' matched actual value '" + toPrinted(actual) + "'");
  }

  var testcase = new TestCase("unknown-test-name", description, expected, actual);
  testcase.reason = output;

  // if running under reftest, let it handle result reporting.
  if (true) {
    if (testcase.passed)
    {
      print(PASSED + description);
    }
    else
    {
      reportFailure (description + " : " + output);
    }
  }
  return testcase.passed;
}

/*
 * Attempt to match a regular expression describing the result to
 * the actual result, if they differ (in value and/or
 * type) report a failure.  If description is provided, include it in the
 * failure report.
 */
function reportMatch (expectedRegExp, actual, description) {
  $ERROR("reportMatch(): Not implemented!")
}

/*
 * Puts funcName at the top of the call stack.  This stack is used to show
 * a function-reported-from field when reporting failures.
 */
function enterFunc (funcName)
{
  callStack.push(funcName);
}

/*
 * Pops the top funcName off the call stack.  funcName is optional, and can be
 * used to check push-pop balance.
 */
function exitFunc (funcName)
{
  var lastFunc = callStack.pop();

  if (funcName)
  {
    if (lastFunc != funcName)
      reportCompare(funcName, lastFunc, "Test driver failure wrong exit function ");
  }
}

/*
 * Peeks at the top of the call stack.
 */
function currentFunc()
{
  return callStack[callStack.length - 1];
}

/*
  Calculate the "order" of a set of data points {X: [], Y: []}
  by computing successive "derivatives" of the data until
  the data is exhausted or the derivative is linear.
*/
function BigO(data)
{
  $ERROR("BigO(): Not implemented!");
}

function compareSource(expect, actual, summary)
{
  $ERROR("compareSource(): Not implemented!");
}

function optionsInit() {
  $ERROR("optionsInit(): Not implemented!");
}

function optionsClear() {
  $ERROR("optionsClear(): Not implemented!");
}

function optionsPush()
{
  $ERROR("optionsPush(): Not implemented!");
}

function optionsPop()
{
  $ERROR("optionsPop(): Not implemented!");
}

function optionsReset() {
  $ERROR("optionsReset(): Not implemented!");
}

function getTestCaseResult(expected, actual)
{
  if (typeof expected != typeof actual)
    return false;
  if (typeof expected != 'number')
    // Note that many tests depend on the use of '==' here, not '==='.
    return actual == expected;

  // Distinguish NaN from other values.  Using x != x comparisons here
  // works even if tests redefine isNaN.
  if (actual != actual)
    return expected != expected;
  if (expected != expected)
    return false;

  // Tolerate a certain degree of error.
  if (actual != expected)
    return Math.abs(actual - expected) <= 1E-10;

  // Here would be a good place to distinguish 0 and -0, if we wanted
  // to.  However, doing so would introduce a number of failures in
  // areas where they don't seem important.  For example, the WeekDay
  // function in ECMA-262 returns -0 for Sundays before the epoch, but
  // the Date functions in SpiderMonkey specified in terms of WeekDay
  // often don't.  This seems unimportant.
  return true;
}

if (typeof dump == 'undefined')
{
  if (typeof window == 'undefined' &&
      typeof print == 'function')
  {
    dump = print;
  }
  else
  {
    dump = (function () {});
  }
}

function test() {
  gTc = 0;
  while (gTc < gTestcases.length) {
    // temporary hack to work around some unknown issue in 1.7
    try
    {
      gTestcases[gTc].passed = writeTestCaseResult(
        gTestcases[gTc].expect,
        gTestcases[gTc].actual,
        gTestcases[gTc].description +" = "+ gTestcases[gTc].actual );
      gTestcases[gTc].reason += ( gTestcases[gTc].passed ) ? "" : "wrong value ";
    }
    catch(e)
    {
      print('test(): empty testcase for gTc = ' + gTc + ' ' + e);
    }
    gTc++;
  }
  stopTest();
  return ( gTestcases );
}

/*
 * Begin printing functions.  These functions use the shell's
 * print function.  When running tests in the browser, these
 * functions, override these functions with functions that use
 * document.write.
 */

function writeTestCaseResult( expect, actual, string ) {
  var passed = getTestCaseResult( expect, actual );
  // if running under reftest, let it handle result reporting.
  if (true) {
    writeFormattedResult( expect, actual, string, passed );
  }
  return passed;
}
function writeFormattedResult( expect, actual, string, passed ) {
  var s = ( passed ? PASSED : FAILED ) + string + ' expected: ' + expect;
  if (passed) {
    print(s);
  } else {
    $ERROR(s);
  }

  return passed;
}

function writeHeaderToLog( string ) {
  print( string );
}
/* end of print functions */


/*
 * When running in the shell, run the garbage collector after the
 * test has completed.
 */

function stopTest() {
  var gc;
  if ( gc != undefined ) {
    gc();
  }
}

/*
 * Convenience function for displaying failed test cases.  Useful
 * when running tests manually.
 *
 */
function getFailedCases() {
  var i = 0;
  while (i < gTestcases.length) {
    if ( ! gTestcases[i].passed ) {
      print( gTestcases[i].description + " = " +gTestcases[i].actual +
             " expected: " + gTestcases[i].expect );
    }
    i++;
  }
}

function jsTestDriverEnd()
{
  // gDelayTestDriverEnd is used to
  // delay collection of the test result and
  // signal to Spider so that tests can continue
  // to run after page load has fired. They are
  // responsible for setting gDelayTestDriverEnd = true
  // then when completed, setting gDelayTestDriverEnd = false
  // then calling jsTestDriverEnd()

  if (gDelayTestDriverEnd)
  {
    return;
  }

  try
  {
    optionsReset();
  }
  catch(ex)
  {
    dump('jsTestDriverEnd ' + ex);
  }

  var i = 0;
  while (i < gTestcases.length)
  {
    gTestcases[i].dump();
    i++;
  }

}

function jit(on)
{
}

/*
 * Some tests need to know if we are in Rhino as opposed to SpiderMonkey
 */
function inRhino()
{
  return (typeof defineClass == "function");
}

/* these functions are useful for running tests manually in Rhino */

function GetContext() {
  return Packages.com.netscape.javascript.Context.getCurrentContext();
}
function OptLevel( i ) {
  i = Number(i);
  var cx = GetContext();
  cx.setOptimizationLevel(i);
}
/* end of Rhino functions */
