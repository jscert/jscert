function foo() {
    var x = 10
    try {
        throw 22;
    }
    catch(e) {
        x = 22
    }
    if (x === 22) {
        print ("passed");
    }
    else if (x === 10) {
      print ("missed catch block");
    }
}
foo();
