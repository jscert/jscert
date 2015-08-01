/**
 * Testing 8.12.4-8-a
 * Data property on a prototype written to with extensions prevented.
 * Covers 652
 */

function testcase() {  
    function foo() {};
    foo.prototype.bar = 0;
    var o = new foo();
    Object.preventExtensions(o);
    o.bar = 1;
    return o.hasOwnProperty("bar") == false && o.bar == 0; 
}
runTestCase(testcase);
