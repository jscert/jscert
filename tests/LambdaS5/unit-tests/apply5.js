function f(obj) { return this.x; }
if(f.apply({x:2}) === 2) {
  print('passed');
}
