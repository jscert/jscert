/**
 * Testing 10.6 (DefineOwnProperty-5-b-ii)
 * While frozen, attempt to redefine a property of the arguments object.
 * Covers 790 793 (by virtue of freeze - unsatisfactory method)
 */

function testcase() {
  function foo(a)
  {
    Object.freeze(arguments);
    arguments[0] = 2;
    return arguments[0] == 1;  
  }
  return foo(1);
 }
runTestCase(testcase);
