function odd(n) {
  return (n === 0) ? false : even(n - 1);
  function even(n) {
    return (n === 0) ? true : odd(n - 1);
  }
}

if (!odd(6) && odd(7) && !odd(8) && odd(9)) {
  console.log("Passed");
}