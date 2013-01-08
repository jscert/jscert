var f = function() {
	var e = "bar";
	with({e:"foo"}) {
	  var e = "wibble";
	};
	actual = e;
}
f();