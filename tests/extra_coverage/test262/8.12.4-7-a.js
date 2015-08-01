/**
 * Testing 8.12.4-7-a
 * Accessor property on a prototype with undefined [[Set]] written to.
 * Covers 654
 */

function testcase() {  
    function foo() {};
    foo.prototype = {get bar() {return 0;}};
    var o = new foo();
    o.bar = 1;
    return o.hasOwnProperty("bar") == false && o.bar == 0; 
}
runTestCase(testcase);
