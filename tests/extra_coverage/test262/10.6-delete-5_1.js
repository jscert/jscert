/**
 * Testing 10.6 (delete-5)
 * Call delete on a non-existent property of the arguments object.
 * Covers 946
 */

function testcase() {
  function foo(a)
  {
    var before = arguments.hasOwnProperty(foo)
    delete arguments.foo;
    return (before == false);  
  }
  return foo(1);
 }
runTestCase(testcase);
