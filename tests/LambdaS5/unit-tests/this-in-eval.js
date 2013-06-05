
var fnGlobalObject = Function("return this;")();

function test1() {
  'use strict';
  var f = Function("return this;");
  return f();
}

function test2() {
  "use strict";
  var f = Function("return typeof this;");
  return f() !== "undefined";
}

if (test1() === fnGlobalObject && test2() === true) {
  console.log("passed");
}
