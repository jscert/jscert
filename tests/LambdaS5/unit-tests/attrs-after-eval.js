(function() {
  (1,eval)("var x;")
})();
console.log(this);
var g = Object.getOwnPropertyDescriptor(this, "x");
if(g.value === undefined && g.writable === true
  && g.configurable === true && g.enumerable === true) {
  console.log("Passed!");
}
