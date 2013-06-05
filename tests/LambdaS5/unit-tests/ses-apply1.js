  function test_BIND_CALLS_APPLY() {
    if (!('bind' in Function.prototype)) { return false; }
    var applyCalled = false;
    function foo() { return [].slice.call(arguments,0).join(','); }
    foo.apply = function fakeApply(self, args) {
      applyCalled = true;
      return Function.prototype.apply.call(this, self, args);
    };
    var b = foo.bind(33,44);
    var answer = b(55,66);
    if (applyCalled) { return true; }
    if (answer === '44,55,66') { return false; }
    return 'Bind test returned "' + answer + '" instead of "44,55,66".';
  }
if(!test_BIND_CALLS_APPLY()) {
  console.log('passed');
}
