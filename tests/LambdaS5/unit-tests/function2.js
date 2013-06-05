function foo(o) {
    function bar(o) {
        return o;
    }
    return bar(o);
}

if(foo(12) === 12) {
    print("passed");
}
