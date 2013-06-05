// If the test passed, then it would have called "print('passed')", which would have caused __$JSRef_PASSED__ to be set to "true".
if(! __$JSRef_PASSED__){
    $ERROR("This test didn't call print('passed')");
}
