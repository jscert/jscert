try {
  var obj = {};
  obj(3);
} catch (e) {
  if (e instanceof TypeError) {
    print("passed");
  }
}
