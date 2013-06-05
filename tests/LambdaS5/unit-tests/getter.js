"use strict";

function g() {
  return this;
}

var StringProto = Object.getPrototypeOf(Object(""));

if (g.call(StringProto) === StringProto) {
  console.log("passed");
}

