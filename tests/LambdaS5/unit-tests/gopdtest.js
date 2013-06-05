var obj = (function() {
    var z = 0;
    return { data : "data",
             get n() { return z; },
             set n(x) { z = x; } };
}());


var accessorPD = Object.getOwnPropertyDescriptor(obj, "n");
var p1 = accessorPD.hasOwnProperty("get") &&
  accessorPD.hasOwnProperty("set") && 
  accessorPD.hasOwnProperty("enumerable") && 
  accessorPD.hasOwnProperty("configurable");

var dataPD = Object.getOwnPropertyDescriptor(obj, "data");
var p2 = dataPD.hasOwnProperty("value") &&
  dataPD.hasOwnProperty("writable") &&
  dataPD.hasOwnProperty("enumerable") &&
  dataPD.hasOwnProperty("configurable");

Object.defineProperty(obj,
    "data2",
    { value : "data2",
      writable : false,
      enumerable : true,
      configurable : false});

var data2PD = Object.getOwnPropertyDescriptor(obj, "data2");
var p3 = data2PD.hasOwnProperty("value") &&
  data2PD.hasOwnProperty("writable") &&
  data2PD.hasOwnProperty("enumerable") &&
  data2PD.hasOwnProperty("configurable") &&
  data2PD.writable === false &&
  data2PD.enumerable === true &&
  data2PD.configurable === false;

if (p1 && p2 && p3) {
  print("passed");
}
