var test = (function foo() {
  var foo = 2;
  return foo;
})();

if(test === 2) { console.log("passed"); }
