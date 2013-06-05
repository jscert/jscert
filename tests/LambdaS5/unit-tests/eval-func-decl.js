function test() {
  "use strict";
  eval("function innerfunc(){}");
  if (typeof innerfunc === "undefined") {
    console.log("passed");
  }
}

test();