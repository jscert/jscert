function test_STRICT_EVAL_LEAKS_GLOBALS() {
  (1,eval)('"use strict"; var ___global_test_variable___ = 88;');
  if ('___global_test_variable___' in window) {
    delete window.___global_test_variable___;
    return true;
  }
  return false;
}

if (test_STRICT_EVAL_LEAKS_GLOBALS() === false) {
  console.log("Passed");
}