var o = Object.create({x: 22});
with(o) {
  if(x === 22) { console.log('passed'); }
}
