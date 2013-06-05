var f = function g(n) {
   if (n === 0) {
      return 0;
   } else {
      return g(n - 1);
   }
}

if (f(3) === 0) {
   print("passed");
}
