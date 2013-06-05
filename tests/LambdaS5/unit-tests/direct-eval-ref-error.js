this.x = 33;
(function() {
  try {
    eval("delete window.x; x;");
  } catch(e) {
    if (e instanceof ReferenceError) {
      console.log('passed');
    }
  }
})();

