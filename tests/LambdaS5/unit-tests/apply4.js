var global = this;
function g() {
  // gets called, but arguments empty
  if(arguments[0] === undefined && this === global) {
    print('passed');
  }
}

g.apply();
