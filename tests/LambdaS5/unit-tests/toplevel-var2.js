var x;

var g = Object.getOwnPropertyDescriptor(this, "x");

if(g.value === undefined && g.writable === true && g.configurable === false && g.enumerable === true) {
  print('Passed!');
}
