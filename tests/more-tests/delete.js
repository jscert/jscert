
// Testing the SyntaxError exception of the delete operator.
// If this test fails completely (without $ERROR) then the exception was non-catchable, and most likely it was detected at parse time rather than at run time as it should have been.

var fun = function (){
    "use strict";
    delete x; // This should throw a SyntaxError exception at call time, not parsing time!
    $ERROR("#1.1: This code should throw a (catchable) SyntaxError exception.")
};

try {
    fun ()
} catch (e){
    if ((e instanceof SyntaxError) !== true){
        $ERROR("#1.2: The exception thrown by this code should have been a SyntaxError exception.");
    }
}


