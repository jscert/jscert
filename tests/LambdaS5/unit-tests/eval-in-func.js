var x = 5;
function g(x) {
  (1,eval)("'use strict';x = 22;")
  return x === 17;
}
if (g(17) && window.x === 22) {
  console.log("Passed");
}
