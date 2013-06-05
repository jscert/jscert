"use strict";

var obj = {};
Object.preventExtensions(obj);

try {
  obj.x = 3;
} catch (e) {
  if (e instanceof TypeError) {
    print("passed");
  }
}
