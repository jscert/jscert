var o = new Object(true);
var b = new Boolean(true);

if (o.valueOf() === true && b.valueOf() === true) {
  print("passed");
}
