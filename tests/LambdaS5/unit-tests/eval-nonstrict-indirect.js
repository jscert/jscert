var global = this;
global.y = "global";
var indirectEval = eval;

var testNonstrictIndirect = (function () {
  var x = "outer";
  return function () {
    var y = "inner";
    var t = indirectEval("var x = y; y;");
    return global.x === "global" && x === "outer" && t === "global";
  }
})()();

if (testNonstrictIndirect) {
  console.log("Passed");
}