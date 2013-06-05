var o = {x: 22, y: 40};
var o2 = {x: 33};
var check;
with(o) {
  with(o2) {
    check = (x === 33) && (y === 40);
  }
}
if(check) { console.log('passed'); }

