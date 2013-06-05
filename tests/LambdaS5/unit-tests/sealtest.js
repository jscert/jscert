"use strict";

var obj = {a : 1};
Object.seal(obj);

try {
  delete obj.a;
} catch (e) {
  var apd = Object.getOwnPropertyDescriptor(obj, "a");
  if ((e instanceof TypeError) && obj.a === 1 && apd.configurable === false) {
    print("passed");
  }
}
