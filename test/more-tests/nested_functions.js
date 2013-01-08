f = function () {
	var x = 3;
	
	g = function() {
		var y = 4;
		r = x + y + z;
	};
};

z = 2;
f();
g();