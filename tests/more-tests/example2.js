a = {b : 1};
with (a) {
        f = function(c){b};
};
a = {b : 2};
f(null);
