var arr = [1, 2, 3, 4];
var squared = arr.map(function(n) { return n * n; });

if (squared[0] === 1 && squared[1] === 4 && squared[2] === 9 && 
    squared[3] === 16 && squared.length === 4) {
  print("passed");
}
