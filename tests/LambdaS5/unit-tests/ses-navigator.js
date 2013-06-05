(function() {
  function test_NEEDS_DUMMY_SETTER() {
    if (NEEDS_DUMMY_SETTER_repaired) { return false; }
    if (typeof navigator === 'undefined') { return false; }
    var ChromeMajorVersionPattern = (/Chrome\/(\d*)\./);
    var match = ChromeMajorVersionPattern.exec(navigator.userAgent);
    if (!match) { return false; }
    var ver = +match[1];
    return ver <= 17;
  }
  /** we use this variable only because we haven't yet isolated a test
   * for the problem. */
  var NEEDS_DUMMY_SETTER_repaired = false;


  if (!test_NEEDS_DUMMY_SETTER()) {
    console.log('passed');
  }
})();

