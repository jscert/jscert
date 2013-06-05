function f() {
  if(arguments[0] === 22) {
    print('passed');
  }
}

f.apply({}, [22]);
