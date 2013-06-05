var x = new Array();
var y = new Array(0,1);
var z = new Array(2,3,4);
var arr = x.concat(y,z);

if (arr.toString() === "0,1,2,3,4") {
  print("passed");
}
