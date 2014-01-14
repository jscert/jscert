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
