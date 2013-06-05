var c1 = 0, c2 = 0, c3 = 0, c4 = 0;

var n = 0;
for (; n < 5; ++n) {
  if ((n % 2) === 0) continue;
  c1 += 1;
}

for (var i = 0; i < 5; ++i) {
  if ((i % 2) === 0) continue;
  c2 += 1;
}

var obj = { a : 0, b : 1, c : 2, d : 3, e : 4 };
for (k in obj) {
  if (((obj[k]) % 2) === 0) continue;
  c3 += 1;
}

for (var k in obj) {
  if (((obj[k]) % 2) === 0) continue;
  c4 += 1;
}

if (c1 === 2 && c2 === 2 && c3 === 2 && c4 === 2) {
  print("passed");
}
