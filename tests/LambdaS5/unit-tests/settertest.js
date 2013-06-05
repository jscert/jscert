function foo() {
   var x = 5;
   function bar() {
      x = 10;
   }
   bar();
   if (x === 10) {
      print("passed");
   }
}
foo();
