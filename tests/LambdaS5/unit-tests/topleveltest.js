var x = 3;
for ((function(){ x = 4 }()); false;) {
  print("loop");
}

if (x === 4) {
  print("passed");
}
