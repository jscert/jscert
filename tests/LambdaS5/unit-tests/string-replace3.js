var calledCount = 0;
var replaced = "aba".replace("a", function() {
  calledCount++;
  return calledCount === 1 ? true : null;
});
if(replaced === "truebnull" && calledCount === 2) {
  console.log('passed');
}

