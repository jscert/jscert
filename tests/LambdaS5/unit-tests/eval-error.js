var supportsStrict;
function fnSupportsStrict() {
    "use strict";
    if (supportsStrict !== undefined) {
        return supportsStrict;
    }
    
    try {
        eval('with ({}) {}'); 
        supportsStrict = false;
    } catch (e) {
        supportsStrict = true;
    }
    return supportsStrict;
}
try {
  if(fnSupportsStrict()) {
    print("Passed.");
  }
  else {
    print("Failed!");
  }
}
catch(e) {
  print("Caught: " + e.message);
}
