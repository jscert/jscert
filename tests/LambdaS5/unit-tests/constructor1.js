function foo() {
}
var o = new foo();
print(typeof foo);
print(typeof foo.prototype);
print(typeof foo.prototype.constructor);
print(typeof o.constructor);
if(o.constructor === foo) {
  print("passed");
}