var global = this;
global.y = "global";

var testNonstrictDirect = (function () {
  var x = "outer";
  return function () {
    var y = "inner";
    var t = eval("var x = y; y;");
    return global.x === undefined && x === "inner" && t === "inner";
  }
})()();

if (testNonstrictDirect) {
  console.log("Passed");
}
