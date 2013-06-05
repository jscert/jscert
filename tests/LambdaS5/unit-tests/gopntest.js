var obj = {a : 1, b : 2, c : 3};
var names = Object.getOwnPropertyNames(obj);
if (names[0] === "a" && names[1] === "b" && names[2] === "c" &&
    names.length === 3) {
  print("passed");
}
