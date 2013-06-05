function testcase() {
  var x = 3;

  function f() {
      "use strict";
      x = this;
      return "a";
  }
  return ("ab".replace("b", f)==="aa") && (x===undefined);
}
if(testcase()) { console.log('passed'); }

