function f1(a) {
   delete a;
   return a;
}

try {
  f1(1);
} catch(e) {
  if (e instanceof SyntaxError) {
     console.log("passed");
  }
}
