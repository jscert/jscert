var global = this;
global.y = "global";

var testStrictDirect = (function () {
  var x = "outer";
  return function () {
    "use strict";
    var y = "inner";
    var t = eval("var x = y; y;");
    return global.x === undefined && x === "outer" && t === "inner";
  }
})()();

if (testStrictDirect) {
  console.log("Passed");
}
