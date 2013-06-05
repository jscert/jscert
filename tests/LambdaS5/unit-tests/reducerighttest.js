var arr = ["a", "b", "c", "d"];
var reducedRight = arr.reduceRight(
    function(prior, current) { return prior + current; }, "z");

if (reducedRight === "zdcba") {
  print("passed");
}
