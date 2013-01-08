a = 1;
obj = {a:2};
with (obj)
{
  var f = function () {a;};
}