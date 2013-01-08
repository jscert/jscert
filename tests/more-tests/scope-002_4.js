a = 1;
obj = {a:2, obj:{a:3}};
with (obj)
{
  with (obj)
  {
    var f = function () {actual = a;};
  }
}
f();