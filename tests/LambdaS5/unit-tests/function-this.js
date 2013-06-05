"use strict";
var f = Function("return typeof this;");
if (f() === "undefined") {
  throw "'this' had incorrect value!";
}
console.log('passed');

