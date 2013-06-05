"use strict";

var obj = {a : 1};
Object.freeze(obj);

try {
  delete obj.a;
} catch (e) {
  try {
    obj.a = "changed";
  } catch (f) {
    var apd = Object.getOwnPropertyDescriptor(obj, "a");
    if ((e instanceof TypeError) && (f instanceof TypeError) && 
        obj.a === 1 && apd.configurable === false && apd.writable === false) {
      print("passed");
    }
  }
}
