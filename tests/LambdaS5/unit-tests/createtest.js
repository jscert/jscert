var parent = { foo : 1 };
var props = { 
  bar : 
    { value : 1,
      writable : false,
      enumerable : false,
      configurable : false},
  baz :
    { value : 2,
      writable : true,
      enumerable : true,
      configurable : true},
  blarg : 
    { get : function() { return 46; },
      set : function(v) { print("set blarg"); },
      enumerable : true,
      configurable : false }
}

var child = Object.create(parent, props);
var c1 = Object.getPrototypeOf(child) === parent;
var c2 = child.foo === 1;
var barpd = Object.getOwnPropertyDescriptor(child, "bar");
var c3 = barpd.value === 1 && barpd.writable === false &&
  barpd.enumerable === false && barpd.configurable === false;

var blargpd = Object.getOwnPropertyDescriptor(child, "blarg");
var c4 = (typeof blargpd.get === "function") && 
  (typeof blargpd.set === "function") && blargpd.enumerable === true && 
  blargpd.configurable === true;

if (c1 && c2 && c3) {
  print("passed");
}
