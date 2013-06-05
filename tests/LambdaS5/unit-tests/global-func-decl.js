function f() {}
if (this.hasOwnProperty("f") && this.f === f) {
  console.log("passed");
}