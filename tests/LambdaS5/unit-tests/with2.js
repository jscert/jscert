var o = {x: 22};
with(o) {
  x = 45;
}
if(o.x === 45) { console.log('passed'); }

