"use strict";
(1,eval)("var foo = 12;");
try {
  x = 5;
} catch(e) {
  if(e instanceof ReferenceError) {
    console.log('passed');
  }
}
