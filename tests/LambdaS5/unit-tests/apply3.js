function g() {
  // should do nothing
}
try {
  g.apply({}, 'foo');
}
catch(e) {
  if(e instanceof TypeError) {
    print('passed');
  }
}
