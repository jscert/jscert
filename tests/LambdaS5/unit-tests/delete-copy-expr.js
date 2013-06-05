var o = {x: 5};
var y = 0;

delete o[(y++,"x")];

if(y === 1 && o.hasOwnProperty("x") === false) {
  console.log('Passed');
}
