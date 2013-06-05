var x = 0;
(x = 1) || (x = 2);

var y = -1;
(y = 0) || (y = 1);

if (x === 1 && y === 1) {
   print("passed");
}
