var x = 0;
var y = 0;
for (x = 0; x < 3; x++) {
   y = y + 1;
   break;
}

if (y == 1) {
   print("passed");
} else {
   print(x);
}
