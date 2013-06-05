function f1(x) {
   return x;

   function x() {
      return 7;
   }
}

var result = f1();

if (typeof(result) === "function") {
   print("passed");
}
