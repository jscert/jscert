function factorial(n) {
  if (n === 0) {
    return 1;
  }
  else {
    return n * factorial(n - 1);
  }
}

if (factorial(5) === 120) {
  console.log("Passed");
}