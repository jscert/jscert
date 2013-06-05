window.x = 5;
try {
  eval("'use strict';delete window.x; x;");
}
catch (e) {
  if (e instanceof ReferenceError) {
    console.log("Passed");
  }
}
