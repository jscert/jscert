var called = false;
var newstr = "a".replace("a", function() { called = true; return "b"; });
if(newstr === "b" && called) {
  console.log('passed');
}

