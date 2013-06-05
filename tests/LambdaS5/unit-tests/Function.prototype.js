var ses;
if(!ses) {
  ses = {};
}
(function() {
  var pt = Function.prototype.call;
  if (typeof pt === 'function') { print('passed'); }
  else { print('failed: ' + typeof pt); }
})();
var Function;

