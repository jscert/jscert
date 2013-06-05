function test_BIND_CANT_CURRY_NEW() {
  function construct(f, args) {
    var bound = Function.prototype.bind.apply(f, [null].concat(args));
    return new bound();
  }
  var d;
  try {
    d = construct(Date, [1957, 4, 27]);
  } catch (err) {
    if (err instanceof TypeError) { return true; }
    return 'Curries construction failed with: ' + err;
  }
  if (typeof d === 'string') { return true; } // Opera
  console.log(d);
  var str = Object.prototype.toString.call(d);
  if (str === '[object Date]') { return false; }
  return 'Unexpected ' + str + ': ' + d;
}

if (test_BIND_CANT_CURRY_NEW() === false) {
  console.log("Passed");
}
