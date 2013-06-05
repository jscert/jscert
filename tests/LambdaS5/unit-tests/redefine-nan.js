var global = this;
var descNaN = Object.getOwnPropertyDescriptor(global, 'NaN');
try {
  Object.defineProperty(global, 'NaN', descNaN);
  console.log("Passed");
}
catch (err) {
  console.log("Failed to redefine NaN to itself with error:", err);
}
