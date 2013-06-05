var C = function(n) {
  this.n = n;
}

var obj = new C(10);
var proto = Object.getPrototypeOf(obj);

if (proto === C.prototype) {
  print("passed");
}
