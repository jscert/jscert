a = 1;
obj = {a:2};
with (obj)
{
  f = function () {actual = a;};
}
f();