var obj = {};

Object.defineProperty(obj, "x", {configurable: false, value: 10, writable: true});

// Should be able to change writable to false
Object.defineProperty(obj, "x", {writable: false});
if (Object.getOwnPropertyDescriptor(obj, "x").writable === false) {
  print("passed");
}
