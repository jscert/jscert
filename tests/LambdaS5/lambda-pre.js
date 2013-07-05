// The LambdaS5 tests use "print('passed')" to indicate success. We catch these, and record the passing information for later.
__$JSRef_PASSED__ = false;
function print(str) {
    if(str==='passed' || str==='Passed.') {
        __$JSRef_PASSED__ = true
    }
}

var console = { log : print }
