function go () {
  var n = 0;
  var obj = {toLocaleString: function() {n++}};
  var arr = [undefined, obj, null, obj, obj];
  arr.toLocaleString();

  if (n === 3) {
    print('passed');
  }  
}

go();
