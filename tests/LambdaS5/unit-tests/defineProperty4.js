var obj = {};

Object.defineProperty(obj, "x", {configurable: false, value: 10, writable: false});

// Shouldn't be able to change value of non-writable
try {
  Object.defineProperty(obj, "x", {value: 4});
}
catch(e) {
  if (e instanceof TypeError) {
    print("passed")
  }
}
