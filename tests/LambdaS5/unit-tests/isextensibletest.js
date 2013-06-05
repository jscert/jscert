var obj = {};
var before = Object.isExtensible(obj);
Object.preventExtensions(obj);
var after = Object.isExtensible(obj);

if (before === true && after === false) {
  print("passed");
}
