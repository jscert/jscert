var obj = { x : "xxx" };

var f = function(a, b) {
  return a + b + (this ? this.x : 'undefined');
}

var boundF = f.bind(obj, "aaa");

var result1 = f("aaa", "bbb");
var result2 = boundF("bbb");

try {
  var q = boundF.caller;
} catch (e) {
  if (e instanceof TypeError) {
    try {
      boundF.caller = null;
    } catch (ee) {
      if (ee instanceof TypeError) {
        try {
          var r = boundF.arguments;
        } catch (eee) {
          if (eee instanceof TypeError) {
            try {
              boundF.arguments = null;
            } catch (eeee) {
              if (eeee instanceof TypeError) {
                if (result1 === "aaabbbundefined" &&
                    result2 === "aaabbbxxx") {
                  print("passed");
                }
              }
            }
          }
        }
      }
    }
  }
}

