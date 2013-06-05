var global = this;
global.y = "global";
var indirectEval = eval;

var testStrictIndirect = (function () {
  var x = "outer";
  return function () {
    var y = "inner";
    var t = indirectEval("'use strict'; var x = y; y;");
    return global.x === undefined && x === "outer" && t === "global";
  }
})()();

if (testStrictIndirect) {
  console.log("Passed");
}