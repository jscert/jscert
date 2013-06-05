var obj = {};
var before = Object.isFrozen(obj);
Object.freeze(obj);
var after = Object.isFrozen(obj);

if (before === false && after === true) {
  print("passed");
}
