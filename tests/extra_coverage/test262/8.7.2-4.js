/**
 * Testing 8.7.2-4
 * Attempt to assign to a property of a primitive.
 * Covers 1092 1161 1162 1191
 */

function testcase() {  
  var foo = 1;
  foo.bar = 1;
  return foo.bar == undefined;
}
runTestCase(testcase);
