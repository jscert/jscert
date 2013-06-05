function foo() {
  this.x = 5;
}

var o = new foo();
if(o.x === 5) {
  print("passed");
}
