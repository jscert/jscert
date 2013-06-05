this.eval = function() {
  if(arguments["0"] === "heyo!" && arguments["1"] === "my friend") {
    console.log("Passed.");
  }
}
eval("heyo!", "my friend");

