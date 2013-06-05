var x = [];
var y = ["zero", "one", "two"];
x.push.apply(x, y);
console.log(x);
if (x.length === 3) {
  console.log("passed");
}
