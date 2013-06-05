function foo(x) {
    if(x === 22) 
    { foo(43); }
    return x;
}

if(foo(22) === 22) {
    print("passed");
}
