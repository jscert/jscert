var x = 5;
function g(x) {
  eval("'use strict';var x = 22;");
  return x === 17;
}
if (g(17) && window.x === 5) {
  console.log("Passed");
}
