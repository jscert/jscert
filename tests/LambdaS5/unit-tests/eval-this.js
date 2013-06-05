var test1 = eval("'use strict';this") === window;
var test2 = eval("'use strict';this") === this;
var result = eval("'use strict';this");
typeof result;
if (test1 && test2) {
  console.log("Passed");
}
