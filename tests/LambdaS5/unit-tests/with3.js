var x = 22;
var o = {x: 33};
var fst = false;
with(o) {
  if(x === 33) { fst = true;}
}
if (x === 22 && fst) { console.log('passed'); }
