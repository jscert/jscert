var x = 1;
var o = {};
with (o)
  x = o.x = 2; 
r = x + o.x;