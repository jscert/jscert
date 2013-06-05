var arr = [1, 2, 3, 4];
var somePos = arr.some(function(n) { return n >= 0; });
if (somePos === true) {
  var someNeg = arr.some(function(n) { return n < 0; });
  if (someNeg === false) {
    print("passed");
  }
}
