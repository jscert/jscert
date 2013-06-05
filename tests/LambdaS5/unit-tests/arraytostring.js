var x = [];
x[0] = 0;
x[3] = 3;
if (x.toString() === "0,,,3" && x.toString() === x.join()) {
  print('passed');
}
