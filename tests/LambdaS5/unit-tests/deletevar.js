function foo() {
  var x = 3;
  delete x;
}

try {
  foo();
} catch(e) {
  if (e instanceof SyntaxError) {
    console.log("passed");
  }
}
