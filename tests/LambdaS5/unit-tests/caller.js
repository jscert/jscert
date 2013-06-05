function foo() {
   "use strict";
    try {
        var a = arguments.caller;
    }
    catch(e) {
        print("passed");
    }
}
foo();
