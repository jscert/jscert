function foo() {
    try {
        throw 5;
    }
    catch(e) {
        if(e === 5) {
            print("passed");
        }
    }
}
foo();
