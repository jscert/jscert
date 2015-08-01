/**
 * Testing 15.2.4.6-1
 * isPrototypeOf a primative is false
 * Covers 3448
 */

function testcase() {  
  var foo = {};
  return !foo.isPrototypeOf(true);
}
runTestCase(testcase);
