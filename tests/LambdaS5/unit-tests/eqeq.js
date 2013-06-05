function foo() {
    var o = {toString : function() { return 1; }};
    if( o == true ) {
        print("passed");
    }
}
foo();
