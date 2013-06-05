var obj = {};
var before = Object.isSealed(obj);
Object.seal(obj);
var after = Object.isSealed(obj);

if (before === false && after === true) {
  print("passed");
}
