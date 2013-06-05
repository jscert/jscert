var __FRST="one";
var __SCND="two";

var __func = function(arg1, arg2){
    this.first=arg1;
    var __gunc = Function.call(this,"arg","return ++arg;");
    __gunc.prop=arg2;
    return __gunc;
};

var __instance = new __func(__FRST, __SCND);
var passed = true;

if (__instance.first !== undefined) {
	passed = false;
}

if (__instance.prop!==__SCND) {
	passed = false;
}

if (__instance(1)!== 2) {
	passed = false;
}

if (passed) {
  print("passed");
}
