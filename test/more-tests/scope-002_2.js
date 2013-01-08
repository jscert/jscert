a = 1;
f = function () {actual = a;};
obj = {a:2};
with (obj)
{
  f();
}