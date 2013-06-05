var x = 198;
eval("'use strict';var x = 222");
if (x === 198) {
  console.log("Passed");
}

var y = 211;
eval("'use strict';y = 233");
if (y === 233) {
  console.log("Passed");
}
