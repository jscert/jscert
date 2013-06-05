/// Copyright (c) 2012 Ecma International.  All rights reserved. 
/// Ecma International makes this code available under the terms and conditions set
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the 
/// "Use Terms").   Any redistribution of this code must retain the above 
/// copyright and this notice and otherwise comply with the Use Terms.

function testcase() {
        "use strict";
        var obj = {};
        Object.defineProperty(obj, "prop", {
            get: function () {
                return 11;
            },
            set: undefined,
            enumerable: true,
            configurable: true
        });

        try {
            obj.prop <<= 20;
            return false;
        } catch (e) {
            return e instanceof TypeError && obj.prop === 11;
        }
    }
if(testcase()) { console.log('passed'); }

