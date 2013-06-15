// Martin's original error function, which sets the secret state. Updated to keep more than one error message.
function $ERROR (str) {
    try {
        __$ERROR__ = __$ERROR__ + " | " + str
    }
    catch(ex) {
        __$ERROR__ = str
    }
}

// Gareth's addition, which brings it up to Test262 conformance. Hopefully.
t262 = {$ERROR:$ERROR , TestFailureError: function(err){return {__$ERROR__:err}}}
TypeError = function(err){return {__$ERROR__:err}}
