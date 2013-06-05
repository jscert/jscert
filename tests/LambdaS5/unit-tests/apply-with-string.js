function testcase() {
        "use strict";

        function fun() {
            console.log("This was:\n")
            console.log(this);
            return (this instanceof String);
        }
        return !fun.apply("", Array);
    }
if(testcase()) {
  console.log("passed");
}
