function bar(x) {
   return function() {
      var x = x;
      return x;
   }
}

if (bar(200)() === undefined) {
   print("passed");
}
