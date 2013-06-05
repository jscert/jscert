var re = /(\w|\$)+/g;
var l = [];
(function foo() {
  a = re.exec("foo bar baz")
  a = re.exec("foo bar baz")
  a = re.exec("foo bar baz")
  console.log(a);
  if (a === null) { return; }
  l.push(a[0]);
  foo();
})();
if (l[0] === "foo" &&
    l[1] === "bar" &&
    l[2] === "baz") {
  console.log("passed");
}

