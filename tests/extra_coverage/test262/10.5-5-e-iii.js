/**
 * Testing 10.5-5-e-iii
 * With the existence of a function in the global scope, for which [[Configurable]] is true, attempt to declare a function in the global scope with an identical identifier.
 * Covers 1674 1680 1686 1687
 */

function testcase() {
(0, eval)("function foo(){return 0};function foo(){return 1};");
return (foo() == 1);  
}
runTestCase(testcase);
