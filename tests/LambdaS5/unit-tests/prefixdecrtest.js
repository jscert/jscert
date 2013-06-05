var x = 3;
--x;

var obj = { y : 4 };
--obj.y

var objj = { z : obj }
--objj.z.y

if (x === 2 && obj.y === 2) {
  print("passed");
}
