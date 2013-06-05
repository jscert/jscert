function foo() {
  return {y : 10};
}

var o = new foo();
if(o.y === 10) {
  print("passed");
}
