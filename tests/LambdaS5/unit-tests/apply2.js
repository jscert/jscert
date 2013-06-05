function g() {
  if(arguments[1] === 'argument 2' && this.foo === 34) {
    print('passed');
  }
}

g.apply({foo:34}, [,'argument 2']);
