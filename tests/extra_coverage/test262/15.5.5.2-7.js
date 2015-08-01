/**
 * Testing 15.5.5.2-7
 * Attempt to access a character index of a string with len ≤ index 
 * Covers 2046
 * Equivalent to ch15/15.5/15.5.5/15.5.5.2/15.5.5.5.2-7-4.js
 */

function testcase() {  
  var foo = "foo";
  var bar = foo[3];
  return bar == undefined;
}
runTestCase(testcase);
