var arr = [1, 2, 3, 4];
var everyPositive = arr.every(function(n) { return n >= 0; });
if (everyPositive === true) {
  var everyEven = arr.every(function(n) { return (n % 2) === 0; });
  if (everyEven === false) {
    print("passed");
  }
}
