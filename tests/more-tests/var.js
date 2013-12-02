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

