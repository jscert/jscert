var obj = {};
Object.defineProperties(obj,
    { "a" : { value : 1, enumerable : true },
      "b" : { value : 2, enumerable : false},
      "c" : { value : 3, enumerable : true },
      "d" : { value : 4, enumerable : false} });

var keys = Object.keys(obj);
if (keys.length === 2 && keys.indexOf("a") >= 0 && keys.indexOf("b") === -1 &&
    keys.indexOf("c") >= 0 && keys.indexOf("d") === -1) {
  print("passed");
}
