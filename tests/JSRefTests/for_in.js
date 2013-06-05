function test0() {
    var title = "The non-enumerable property should shield us from the enumerable one";
    var expected = "This is a bug in V8, LambdaS5, IE and WebKit. SpiderMonkey and Opera are fine. ";
    var ret = "shadowing works";
    var b = { };
    Object.defineProperty(b, 'y', {value: 2, enumerable: true});
    var a = { };
    Object.defineProperty(a, 'y', {value: 1, enumerable: false});
    a.__proto__ = b;
    for (var i in a) {
        ret = "shadowing fails. We saw "+a[i];
        $ERROR(ret);
    }
    return title+"\n"+expected+"\n"+ret;
}

function test1() {
    var title = "Deleting a property that hasn't appeared will prevent it from appearing.";
    var expected = "This works in V8, LambdaS5, Opera, IE and WebKit, but not in SpiderMonkey.";
    var ret = "w did not appear";
    var deleted_w_yet = false;
    var c = {z:4, w:5, t:6, u:7};

    var b = {y:3};

    b.__proto__ = c;

    var a = {x:1, t:2};

    a.__proto__ = b;

    for (var i in a) {
        if (i == "z") {deleted_w_yet = delete(c.w);}
        if (i =="w") {
            if (deleted_w_yet) {ret = "w appeared after we deleted it";$ERROR(ret);}
            else {ret = "We didn't delete w fast enough. This test is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test1a() {
    var title = "Deleting a property that hasn't appeared will prevent it from appearing.";
    var expected = "This works in V8, Opera, WebKit, IE, and SpiderMonkey, but not LambdaS5.";
    var ret = "w did not appear";
    var deleted_w_yet = false;
    var a = {z:4, w:5, t:6, u:7};

    for (var i in a) {
        if (i == "z") {deleted_w_yet = delete(a.w);}
        if (i =="w") {
            if (deleted_w_yet) {ret = "w appeared after we deleted it";$ERROR(ret);}
            else {ret = "We didn't delete w fast enough. This test is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test1b() {
    var title = "Deleting a property that hasn't appeared *from a prototype* will prevent it from appearing.";
    var expected = "This works in V8, Opera, IE, and WebKit, but not in SpiderMonkey or LambdaS5.";
    var ret = "w did not appear";
    var deleted_w_yet = false;
    var b = {z:4, w:5, t:6, u:7};
    var factory = function(){};
    factory.prototype = b;
    var a = new factory();

    for (var i in a) {
        if (i == "z") {deleted_w_yet = delete(b.w);}
        if (i =="w") {
            if (deleted_w_yet) {ret = "w appeared after we deleted it";$ERROR(ret);}
            else {ret = "We didn't delete w fast enough. This test is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test2() {
    var title = "Deleting a property that hasn't appeared may reveal shadowed properties";
    var expected = "We see this in V8, Opera, WebKit and SpiderMonkey. In LambdaS5 something odd happened. In IE something that 'shouldn't' happened";
    var ret = "t did not appear. This shouldn't happen.";
    var deleted_t_yet = false;
    var c = {z:4, w:5, t:6, u:7};

    var b = {y:3};

    b.__proto__ = c;

    var a = {x:1, t:2};

    a.__proto__ = b;

    for (var i in a) {
        if (i == "x") {deleted_t_yet = delete(a.t);}
        if (i =="t") {
            if (deleted_t_yet && a[i]===6) {
                ret = "The shadowed t appeared after we deleted the local one.";
            }
            else if (deleted_t_yet && a[i]!==6){
                ret = "Something very odd happened. Did deleting fail, but report success?";
            }
            else { ret = "We didn't delete t fast enough. This test is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test2a() {
    var title = "Deleting a property which was shadowing a non-enumerable probably shouldn't expose the non-enumerable property";
    var expected = "V8, Opera and WebKit disagree with us, but SpiderMonkey and IE do not. In LambdaS5 the test was invalid";
    var ret = "the non-enumerable property was not enumerated";
    var deleted_z_yet = false;
    var a = {};
    Object.defineProperty(a, 'z', {value: 'secret', enumerable: false});
    var b = {x:0, z:"tricky", __proto__:a};
    for (var i in b) {
        if(i=='x') {
            deleted_z_yet = delete b.z ;
        }
        if (i=='z') {
            if(deleted_z_yet) { ret = "the non-enumerable property was enumerated";$ERROR(ret);}
            else { ret = "We didn't delete z fast enough. This run is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test3() {
    var title = "Changing prototypes may reveal new properties";
    var expected = "We don't see this in V8, Opera, WebKit, LambdaS5, IE or SpiderMonkey (see also tests 3b and 3c)";

    var ret = "no new properties were revealed";
    var c = {z:4, w:5, t:6, u:7};

    var b = {y:3};

    b.__proto__ = c;

    var a = {x:1, t:2};

    a.__proto__ = b;

    for (var i in a) {
        if (i == "z") {a.__proto__={foo:123, u:567};}
        if (i == "foo") {ret = "the property 'foo' was revealed";}
    }
    return title+"\n"+expected+"\n"+ret;
}

function test3a() {
    var title = "Changing prototypes probably shouldn't expose the non-enumerable properties. But nothing in the spec outright outlaws it.";
    var expected = "In V8, Opera, WebKit and SpiderMonkey we can't even expose enumerable ones. LambdaS5 and IE seem to do the right thing.";
    var ret = "the non-enumerable property was not enumerated";
    var switched_proto_yet = false;
    var a = {};
    Object.defineProperty(a, 'z', {value: 'secret', enumerable: false});
    var b = {x:0, z:"tricky"};
    var c = {__proto__:b};
    for (var i in c) {
        if(i=='x') {
            c.__proto__ = a;
        }
        if (i=='z') {
            if(switched_proto_yet) { ret = "the non-enumerable property was enumerated";}
            else { ret = "We didn't switch prototypes fast enough. This test is invalid.";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test3b() {
    var title = "Changing prototypes may reveal new properties, take 2.";
    var expected = "We still don't see this in V8, Opera, WebKit, LambdaS5, IE or SpiderMonkey. ";

    var ret = "no new properties were revealed";

    var a = {a:1, aa:2, aaa:3};

    for (var i in a) {
        if (i == "a") {a.__proto__={z:123, zz:567};}
        if (i == "zz") {ret = "the property 'zz' was revealed";}
    }
    return title+"\n"+expected+"\n"+ret;
}

function test3c() {
    var title = "Changing prototypes may reveal new properties, take 3.";
    var expected = "We *still* don't see this in V8, Opera, WebKit, LambdaS5, IE or SpiderMonkey";

    var ret = "no new properties were revealed";

    var a = {a:1, aa:2, aaa:3};
    var b = {__proto__:a};

    for (var i in b) {
        if (i == "a") {b.__proto__={z:123, zz:567};}
        if (i == "zz") {ret = "the property 'zz' was revealed";}
    }
    return title+"\n"+expected+"\n"+ret;
}


function test4() {
    var title = "Added properties may be enumerated later";
    var expected = "V8, Opera, WebKit and SpiderMonkey enumerate them in this test. LambdaS5 and IE do not.";
    var ret = "the added property was not enumerated";
    var added_u_yet = false;
    var c = {z:4, w:5, t:6, u:7, r:8};

    var b = {y:3};

    b.__proto__ = c;

    var a = {x:1, t:2};

    a.__proto__ = b;

    for (var i in a) {
        if (i == "z") {delete(c.u);}
        if (i == "w") {b.u = 555 ; added_u_yet = true;}
        if (i == "u" && added_u_yet) {ret = "the added property was enumerated";}
    }
    return title+"\n"+expected+"\n"+ret;
}

function test5() {
    var title = "Added properties may not be enumerated later";
    var expected = "None of V8, Opera, WebKit, LambdaS5, IE or SpiderMonkey enumerate them in this test.";
    var ret = "the added property was not enumerated";
    var added_u_yet = false;
    var c = {z:4, w:5, t:6, u:7, r:8};

    var b = {y:3};

    b.__proto__ = c;

    var a = {x:1, t:2};

    a.__proto__ = b;

    for (var i in a) {
        if (i == "z") {delete(c.u);}
        if (i == "r") {b.u = 555 ; added_u_yet = true;}
        if (i == "u" && added_u_yet) {ret = "the added property was enumerated";}
    }
    return title+"\n"+expected+"\n"+ret;
}

function test6() {
    var title = "Properties that become non-enumerable shouldn't be enumerated";
    var expected = "SpiderMonkey, WebKit, Opera and V8 all enumerate the non-enumerable thing. IE does the right thing. In LambdaS5 this was invalid.";
    var ret = "The non-enumerable property was not enumerated";
    var modded_a_yet = false;
    var a = {x:4,y:5};
    for (var i in a) {
        if (i=="x") {
            modded_a_yet = Object.defineProperty(a, 'y', {enumerable: false});
        }
        if (i=="y") {
            if(modded_a_yet) { ret = "Looks like we enumerated something non-enumerable";$ERROR(ret);}
            else {ret = "We didn't make it non-enumerable fast enough. This test is invalid";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}

function test7() {
    var title = "Properties that become enumerable may or may not be enumerated";
    var expected = "None of SpiderMonkey, V8, Opera, LambdaS5, IE or WebKit enumerate the newly-enumerable thing.";
    var ret = "The newly enumerable property was not enumerated";
    var modded_a_yet = false;
    var a = {x:4,y:5};
    Object.defineProperty(a, 'y', {enumerable: false});
    for (var i in a) {
        if (i=="x") {
            modded_a_yet = Object.defineProperty(a, 'y', {enumerable: true});
        }
        if (i=="y") {
            if(modded_a_yet) { ret = "Looks like we enumerated something the newly enumerable property";}
            else {ret = "We haven't made it enumerable yet, but we're still enumerating it?";}
        }
    }
    return title+"\n"+expected+"\n"+ret;
}


"test0: " +test0()
    +"\ntest1: "+test1()
    +"\ntest1a: "+test1a()
    +"\ntest1b: "+test1b()
    +"\ntest2: "+test2()
    +"\ntest2a: "+test2a()
    +"\ntest3: "+test3()
    +"\ntest3a: "+test3a()
    +"\ntest3b: "+test3b()
    +"\ntest3c: "+test3c()
    +"\ntest4: "+test4()
    +"\ntest5: "+test5()
    +"\ntest6: "+test6()
    +"\ntest7: "+test7();
