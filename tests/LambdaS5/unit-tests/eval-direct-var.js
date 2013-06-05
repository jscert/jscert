var f = function() {
  var x = 22;
  var t = eval("var x; x;");
  return t === 22;
}

if(f()) { console.log("Passed."); }
else { console.log("We expect this to fail until non-strict mode is implemented.  Future regression ftw."); }

