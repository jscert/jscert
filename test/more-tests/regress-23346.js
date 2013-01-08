var CALL_CALLED = \"PASSED\";

call = function ()
{
  r = CALL_CALLED;
};

f = function (x)
{
  if (x) {
    call();
  }
  else { 
    r = \"FAILED!\";
  }
};

f(true);