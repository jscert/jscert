var obj = {"a" : 1, "b" : 2};
delete obj.a;

delete obj["b"];

var a = ["first", "second", "third"];
delete a[1];

if (obj.a === undefined && obj["b"] === undefined && a[1] === undefined) {
   print("passed");
}
