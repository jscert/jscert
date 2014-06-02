
// Testing the SyntaxError exception of the delete operator.

var fun = function (){
    "use strict";
    delete fundfd; // This should throw a SyntaxError exception at call time.
    $ERROR("#1.1: This code should return a SyntaxError exception.")
};

try {
    fun ()
} catch (e){
    if ((e instanceof SyntaxError) !== true){
        $ERROR("#1.2: This code should return a SyntaxError exception.");
    }
}

// TODO: Check other forms of strict mode and delete form.

