function foo() {
    var x = 10
    try {
        throw 22;
    }
    catch(x) {
        x = 22
    }
    if (x === 10) {
        print ("passed");
    }
}
foo();
