var re = /(\w|\$)+/g;
var l = [];
var a;
a = re.exec("foo bar baz")
l.push(a[0]);
a = re.exec("foo bar baz")
l.push(a[0]);
a = re.exec("foo bar baz")
l.push(a[0]);
console.log(l);
if (l[0] === "foo" &&
    l[1] === "bar" &&
    l[2] === "baz") {
  console.log("passed");
}

