try {
  var o = new Object.prototype;
} catch(e) {
  if (e instanceof TypeError) {
    print("passed");
  }
}
