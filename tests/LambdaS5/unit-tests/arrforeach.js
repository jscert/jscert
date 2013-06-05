var arr = ["a", "b", "", "cde", "fg"];
var to = [];
arr.forEach(function(elt, indx) {
    to.push(elt);
    to.push(indx);
});

if (to.toString() === "a,0,b,1,,2,cde,3,fg,4") {
  print("passed");
}
