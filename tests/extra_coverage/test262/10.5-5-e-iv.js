/**
 * Testing 10.5-5-e-iv
 * Attempt to declare a function in the global scope with an identical identifier to an existing, non-writable global variable.
 * Covers 1696
 */
function testcase() {
  try {
    (0, eval)("function NaN(){return 1};");
  }
  catch (e){
    return true;
  }
  return false;
}
runTestCase(testcase);
