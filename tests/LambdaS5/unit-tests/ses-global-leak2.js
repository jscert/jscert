(function(global) {
  function testGlobalLeak(desc, that) {
    if (that === void 0) { return false; }
    if (that === global) { return true; }
    if ({}.toString.call(that) === '[object Window]') { return true; }
    return desc + ' leaked as: ' + that;
  }

  function test_GLOBAL_LEAKS_FROM_GLOBALLY_CALLED_BUILTINS() {
    global.___global_valueOf_function___ = {}.valueOf;
    var that = 'dummy';
    try {
      that = ___global_valueOf_function___();
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'valueOf() threw: ' + err;
    } finally {
      delete global.___global_valueOf_function___;
    }
    if (that === void 0) {
      // Should report as a safe spec violation
      return false;
    }
    return testGlobalLeak('Global valueOf()', that);
  }

  if(!test_GLOBAL_LEAKS_FROM_GLOBALLY_CALLED_BUILTINS()) {
    console.log('Passed');
  }

})(this);
