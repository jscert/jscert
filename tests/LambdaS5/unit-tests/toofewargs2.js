function f1(x) {
   var x;
   
   return typeof x;
}

var result = !(f1() === "undefined");
if (result === false) {
   print("passed");
}
