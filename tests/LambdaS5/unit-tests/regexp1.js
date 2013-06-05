function mkRe() {
  return /0|[1-9][0-9]*/g;
}

var startswithletters = mkRe().test("asdf456");
var justnums = mkRe().test("456");
var numsthenletters = mkRe().test("456abc");
var onlyletters = mkRe().test("iasu;");

if(startswithletters && justnums && numsthenletters && !onlyletters) {
  console.log('Passed!');
}
