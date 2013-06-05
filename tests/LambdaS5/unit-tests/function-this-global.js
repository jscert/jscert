function testcase() {
"use strict";
var f = Function("return typeof this;");
return f() !== "undefined";
}
if(testcase()) {
  console.log('passed');
}

