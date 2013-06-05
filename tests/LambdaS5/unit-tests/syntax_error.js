var o = {
    test: function testcase() {
        "use strict";

        try {
            eval("var _13_1_9_fun = function (param1, param2, param1) { };");
            return false;
        } catch (e) {
            return e instanceof SyntaxError;
        }
    },
};

if(o.test()) {
  print("Passed.");
}
else {
  console.log("We expect this to fail until non-strict mode is implemented.  Future regression ftw.");
}
