var makeC = function() {
    var i = 0;
    return function() { 
      if (i < 3) { 
        i += 1; 
        return true;
      } else {
        return false;
      }
    };
}

var c1 = makeC();
var whileLoopCount = 0, doWhileLoopCount = 0;

while (c1()) {
  whileLoopCount += 1;
}

var c2 = makeC();

do {
  doWhileLoopCount += 1;
} while (c2());

if (whileLoopCount === 3 && doWhileLoopCount === 4) {
  print('passed');
}
