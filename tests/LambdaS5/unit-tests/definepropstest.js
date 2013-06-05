var original = {};

var result = Object.defineProperties(original,
    { foo : {value : 10, writable : false},
      bar : {value : false, enumerable : false},
      baz : {value : null, configurable : false},
      blarg : { get : function() { return "blarg"; },
                set : function(v) { print("set blarg"); } }
    });

var foopd = Object.getOwnPropertyDescriptor(result, "foo");
var c1 = foopd.value === 10 && foopd.writable === false;
var barpd = Object.getOwnPropertyDescriptor(result, "bar");
var c2 = barpd.value === false && barpd.enumerable === false;
var bazpd = Object.getOwnPropertyDescriptor(result, "baz");
var c3 = bazpd.value === null && bazpd.configurable === false;
var blargpd = Object.getOwnPropertyDescriptor(result, "blarg");
var c4 = (typeof blargpd.get === "function") &&
  (typeof blargpd.set === "function");

if (c1 && c2 && c3 && c4) {
  print("passed");
}
