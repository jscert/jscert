eval("'use strict';window.x = 33");
eval("'use strict';this.y = 77");

if (x === 33 && y === 77) {
  console.log("Passed");
}
