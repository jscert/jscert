var x = [1, 2];
Object.freeze(x);
try {
  x.pop();
}
catch (e) {
  console.log("passed");
}
