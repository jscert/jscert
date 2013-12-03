// I found no test checking for var's behaviours, there are some. -- Martin.

(function (){

    try {
        if (x1 !== undefined)
            $ERROR ("#1.1: 'x1' should be equal to undefined.")
    } catch (e){
        $ERROR ("#1.2: 'x1' should be defined." + e);
    }

    try {
        if (x2 !== undefined)
            $ERROR ("#1.3: 'x2' should be equal to undefined.")
    } catch (e){
        $ERROR ("#1.4: 'x2' should be defined." + e);
    }

    var x1, x2 = 0;


    try {
        if (x3 !== undefined)
            $ERROR ("#2.1: 'x3' should be equal to undefined.")
    } catch (e){
        $ERROR ("#2.2: 'x3' should be defined." + e);
    }

    try {
        if (x4 !== undefined)
            $ERROR ("#2.3: 'x4' should be equal to undefined.")
    } catch (e){
        $ERROR ("#2.4: 'x4' should be defined." + e);
    }

    try {
        if (x5 !== undefined)
            $ERROR ("#2.5: 'x5' should be equal to undefined.")
    } catch (e){
        $ERROR ("#2.6: 'x5' should be defined." + e);
    }

    try {
        if (x6 !== undefined)
            $ERROR ("#2.7: 'x6' should be equal to undefined.")
    } catch (e){
        $ERROR ("#2.8: 'x6' should be defined." + e);
    }

    for (var x3, x4 = 0;false;)
        var x5, x6 = 0;


    try {
        if (x7 !== undefined)
            $ERROR ("#3.1: 'x7' should be equal to undefined.")
    } catch (e){
        $ERROR ("#3.2: 'x7' should be defined." + e);
    }

    try {
        if (x8 !== undefined)
            $ERROR ("#3.3: 'x8' should be equal to undefined.")
    } catch (e){
        $ERROR ("#3.4: 'x8' should be defined." + e);
    }

    try {
        if (x9 !== undefined)
            $ERROR ("#3.5: 'x9' should be equal to undefined.")
    } catch (e){
        $ERROR ("#3.6: 'x9' should be defined." + e);
    }

    for (var x7 in {})
        var x8, x9 = 0;


    try {
        if (x10 !== undefined)
            $ERROR ("#4.1: 'x10' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.2: 'x10' should be defined." + e);
    }

    try {
        if (x11 !== undefined)
            $ERROR ("#4.3: 'x11' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.4: 'x11' should be defined." + e);
    }

    try {
        if (x12 !== undefined)
            $ERROR ("#4.5: 'x12' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.6: 'x12' should be defined." + e);
    }

    try {
        if (x13 !== undefined)
            $ERROR ("#4.7: 'x13' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.8: 'x13' should be defined." + e);
    }

    try {
        if (x14 !== undefined)
            $ERROR ("#4.9: 'x14' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.10: 'x14' should be defined." + e);
    }

    try {
        if (x15 !== undefined)
            $ERROR ("#4.11: 'x15' should be equal to undefined.")
    } catch (e){
        $ERROR ("#4.12: 'x15' should be defined." + e);
    }

    try {
        var x10, x11 = 0;
    } catch (_) {
        var x12, x13 = 0;
    } finally {
        var x14, x15 = 0;
    }

}())

