var x = [];
var len1 = x.length;

x[0] = 0;
var len2 = x.length;

x[1] = 0;
var len3 = x.length;

x[246] = 0;
var len4 = x.length;

x[2] = 0;
var len5 = x.length;

if (len1 === 0 && len2 === 1 && len3 === 2 && len4 === 247 && len5 === 247) {
  print('passed');
}
