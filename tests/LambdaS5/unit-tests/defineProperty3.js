var obj = {};

Object.defineProperty(obj, "x", {configurable: false, value: 10});

// Shouldn't be able to change enumerable to true
try {
  Object.defineProperty(obj, "x", {enumerable: true});
}
catch(e) {
  if (e instanceof TypeError) {
    print("passed")
  }
}