// Martin's original error function, which sets the secret state.
function $ERROR (str) {
  __$ERROR__ = str
}

// Gareth's addition, which brings it up to Test262 conformance. Hopefully.
t262 = {$ERROR:$ERROR , TestFailureError: function(err){return {__$ERROR__:err}}}

