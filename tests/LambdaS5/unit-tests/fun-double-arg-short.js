function testcase()
{ 
  try {
    Function('a','a','return;');
    return true;
  } catch (e) {
    console.log(e);
    return false;
  }
 }
if(testcase()) {
  console.log("passed");
}

