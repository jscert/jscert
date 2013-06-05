function f1() {
   var x;

   return x;
}

var result = !(f1() === undefined);
if (result === false) {
   print("passed");
}
