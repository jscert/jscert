var arr = [1, 2, 3, 4];
var reduced = arr.reduce(function(prior, current) { return prior + current; }, 0);

if (reduced === 10) {
  print("passed");
}
