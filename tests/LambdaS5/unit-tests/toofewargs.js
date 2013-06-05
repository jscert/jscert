function f1(a, b) {
   return (b === undefined);
}

var result = !(f1(1, 2) === false);
if (result === false) {
   print("passed");
}
