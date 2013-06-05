function f() { "use strict"; return this===undefined;};
if (! (Function("return f();")())){
  throw "'this' had incorrect value!";
}
console.log("passed");