(function(global) {
  "use strict";
  function testGlobalLeak(desc, that) {
    if (that === void 0) { return false; }
    if (that === global) { return true; }
    if ({}.toString.call(that) === '[object Window]') { return true; }
    return desc + ' leaked as: ' + that;
  }
  function test_GLOBAL_LEAKS_FROM_GLOBAL_FUNCTION_CALLS() {
    global.___global_test_function___ = function() { return this; };
    var that = ___global_test_function___();
    delete global.___global_test_function___;
    return testGlobalLeak('Global func "this"', that);
  }
  if(!test_GLOBAL_LEAKS_FROM_GLOBAL_FUNCTION_CALLS()) {
    console.log('Passed');
  }
})(this);
