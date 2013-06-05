var obj = {};

Object.defineProperty(obj, "x", {configurable: true, value: 10, writable: false});

var f = function() { return 22; };
// Should be able to change to an accessor
Object.defineProperty(obj, "x", {get: f});
var desc = Object.getOwnPropertyDescriptor(obj, "x");
if (
    desc.writable === undefined &&
    desc.get === f &&
    desc.set === undefined &&
    desc.configurable === true &&
    desc.enumerable === false &&
    obj.x === 22
  ) {
  print("passed");
}
