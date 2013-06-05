var x = 5;
eval("'use strict';window.y = x; var x;");
console.log(typeof window.hasOwnProperty);
if (window.y === undefined && window.hasOwnProperty("y") && window.x === 5) {
  console.log("Passed");
}
