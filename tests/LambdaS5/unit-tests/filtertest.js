var arr = [1, 2, 3, 4];
var filtered = arr.filter(function(n) { return (n % 2) === 0; });

if (filtered.length === 2 && filtered.indexOf(1) === -1 && 
    filtered.indexOf(2) >= 0 && filtered.indexOf(3) === -1 &&
    filtered.indexOf(4) >= 0) {
  print("passed");
}
