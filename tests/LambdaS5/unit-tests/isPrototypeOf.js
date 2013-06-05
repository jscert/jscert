function foo() {

}
var foozle = {};
foo.prototype = foozle;
var o = new foo();

if(foozle.isPrototypeOf(o)) {
  print("passed");
}
print(foozle.isPrototypeOf(o));