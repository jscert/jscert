var makeCounter = function(init) {
  var count = init;

  var counter = function() {
    count +=1;
    return count;
  }

  return counter;
}

var c1 = makeCounter(0),
    c2 = makeCounter(0),
    s = "";

s += c1();
s += c1();
s += c1();

s += c2();
s += c2();
s += c2();

if(s === '123123') {
  print("passed");
}
