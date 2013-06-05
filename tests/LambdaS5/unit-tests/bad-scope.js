var i = 0;
var j = 0;

function f(i) {
  j += i;
  return i;
}

var result = f(1);
j += result
if(j === 2) { print("passed"); }
