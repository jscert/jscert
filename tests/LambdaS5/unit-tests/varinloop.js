function foo() {
  var n = 0;
  var arr = [];
  for(var i = 0; i<5; i++) {
    var n = i + n;
    arr[i] = n;
  }
  return arr;
}
var a = foo();
if(String(a) === '0,1,3,6,10') {
  print('passed');
}

