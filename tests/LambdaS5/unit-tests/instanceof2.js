function Bar() {

}
var o = {}
Bar.prototype = o;
function Foo() {

}

Bar.prototype = new Foo();

var o2 = new Bar();

if(o2 instanceof Foo) {
    print("passed");
}
