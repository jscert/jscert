var o = new Object("strrr");
var s = new String("ssss");

if (s.valueOf() === "ssss" && o.valueOf() === "strrr") {
  print("passed");
}
