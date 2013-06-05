var x = 3;
++x;

var obj = { y : 4 };
++obj.y

var objj = { z : obj }
++objj.z.y

if (x === 4 && obj.y === 6) {
  print("passed");
}
