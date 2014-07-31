/**
 * Testing 10.6 (delete-5)
 * While frozen, attempt to delete a property of the arguments object that exists but is not mapped.
 * Covers 953
 */

function testcase() {
  function foo(a)
  {
    arguments.foo = 1;
    Object.freeze(arguments);
    delete arguments.foo;
    return (arguments.foo = 1);  
  }
  return foo(1);
 }
runTestCase(testcase);
