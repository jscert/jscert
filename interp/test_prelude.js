// Martin's original error function, which sets the secret state. Updated to keep more than one error message.
// We use a try for the first time we set __$ERROR__: as it is not set
// initially, trying to access it will result in an exception.
function $ERROR (str) {
    try {
        __$ERROR__ = __$ERROR__ + " | " + str
    }
    catch(ex) {
        __$ERROR__ = str
    }
}

// Some tests use this instead
var $FAIL = $ERROR

// Gareth's addition, which brings it up to Test262 conformance. Hopefully.
var t262 = {$ERROR:$ERROR , TestFailureError: function(err){return {__$ERROR__:err}}}
var Test262Error = function (){}
// TypeError = function(err){return {__$ERROR__:err}}
function runTestCase(f) {
    if (!f()) {
        $ERROR("runTestCase returned false")
    }
}

// Used in some places to fetch the global object
function fnGlobalObject() {
    return this
}

// Used to test if argument is a function
// taken from test262/harness/fnExists.js
function fnExists(/*arguments*/) {
    for (var i = 0; i < arguments.length; i++) {
        if (typeof (arguments[i]) !== "function") return false;
    }
    return true;
}

// This could be used to print ...
function $PRINT(s){ }

