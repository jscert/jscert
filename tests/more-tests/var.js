// I found no test checking for var's behaviours, there are some. -- Martin.

try {
    if (x !== undefined)
        $ERROR ("#1.1: 'x' should be equal to undefined.")
} catch (e){
    $ERROR ("#1.2: 'x' should be defined." + e);
}

var x = 1;


try {
    if (y !== undefined)
        $ERROR ("#2.1: 'y' should be equal to undefined.")
} catch (e){
    $ERROR ("#2.2: 'y' should be defined." + e);
}

try {
    if (z !== undefined)
        $ERROR ("#2.3: 'z' should be equal to undefined.")
} catch (e){
    $ERROR ("#2.4: 'z' should be defined." + e);
}

for (var y = 0, z = 0;false;);


try {
    if (a !== undefined)
        $ERROR ("#3.1: 'a' should be equal to undefined.")
} catch (e){
    $ERROR ("#3.2: 'a' should be defined." + e);
}

for (var a in {});


// The same wrapped inside an [eval].

eval("\
try {\
    if (b !== undefined)\
        $ERROR (\"g#4.1: 'b' should be equal to undefined.\")\
} catch (e){\
    $ERROR (\"g#4.2: 'b' should be defined.\" + e);\
}\
\
var b = 1;\
\
\
try {\
    if (c !== undefined)\
        $ERROR (\"g#5.1: 'c' should be equal to undefined.\")\
} catch (e){\
    $ERROR (\"g#5.2: 'c' should be defined.\" + e);\
}\
\
try {\
    if (d !== undefined)\
        $ERROR (\"g#6.3: 'd' should be equal to undefined.\")\
} catch (e){\
    $ERROR (\"g#6.4: 'd' should be defined.\" + e);\
}\
\
for (var c = 0, d = 0;false;);\
\
\
try {\
    if (f !== undefined)\
        $ERROR (\"g#7.1: 'f' should be equal to undefined.\")\
} catch (e){\
    $ERROR (\"g#7.2: 'f' should be defined.\" + e);\
}\
\
for (var f in {});\
");

// TODO:  the same in strict mode.

// TODO:  the same wrapped inside a function (named or not).

// TODO:  the same wrapped insade a for, for-var, for-in and for-in-var.

