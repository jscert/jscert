function foo() {
   if (true) {
      var x = 10;
   }
   return x;
}

if (foo() === 10) {
   print("passed");
}
