var x = 3;
var r1 = x++;

var obj = { y : 4 };
var r2 = obj.y++;

if (x === 4 && obj.y === 5 && r1 === 3 && r2 === 4) {
  print("passed");
}
