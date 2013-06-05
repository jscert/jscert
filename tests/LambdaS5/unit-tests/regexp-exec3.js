var re = /(\w|\$)+/g;
if (re.exec("foo bar baz")[0] === "foo" &&
    re.exec("foo bar baz")[0] === "bar" &&
    re.exec("foo bar baz")[0] === "baz") {
  console.log("passed");
}

