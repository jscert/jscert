var desc = Object.getOwnPropertyDescriptor(Number.prototype.toString, "length");
if (desc.enumerable === false && desc.writable === false && desc.configurable === false) {
  console.log("Passed");
}