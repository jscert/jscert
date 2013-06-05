var global = this;
global.y = "global";

var testStrictDirect = (function () {
  var x = "outer";
  return function () {
    var y = "inner";
    var t = eval("'use strict'; var x = y; y;");
    return global.x === undefined && x === "outer" && t === "inner";
  }
})()();

if (testStrictDirect) {
  console.log("Passed");
}