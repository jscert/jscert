var x = 1;

if (this.x !== 1) {
  throw("#1: variable x is a property of global object");
}

try {
  if(delete this.x !== false){
    throw("#2: variable x has property attribute DontDelete");
  }
} catch(e) {
  if(x === 1 && e instanceof TypeError) {
    console.log('passed');
  }
}

