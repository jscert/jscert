var o = {"a" : 0, "b" : 1, "c" : 3};
var count = 0;

for (var x in o) {
   count = count + 1;
}

if (count === 3) {
   print("passed");
}
