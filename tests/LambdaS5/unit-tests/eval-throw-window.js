try {
  eval("'use strict';throw this;");
}
catch (e) {
  if (e === window) {
    console.log("Passed");
  }
}
