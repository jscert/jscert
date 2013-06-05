var notcalled = true;
var replaced = "a".replace("b", function() { notcalled = false; });
if(replaced === "a" && notcalled) {
  console.log('passed');
}

