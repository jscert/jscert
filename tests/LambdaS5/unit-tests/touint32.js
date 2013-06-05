var obj = {};
obj.join = Array.prototype.join;
obj[0] = "x";
obj[1] = "y";
obj[2] = "z";
obj.length = -4294967294;

if (obj.join("") === "xy") {
  print('passed');
}
