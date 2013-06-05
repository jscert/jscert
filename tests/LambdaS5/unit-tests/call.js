function f(x, y) {
  return this + x + y;
}

if (f.call(2, 3, 4) === 9) {
  console.log("passed");
}
