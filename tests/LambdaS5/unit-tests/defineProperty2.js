var o = {}
Object.defineProperty(o, "x", {get: function(asdf) { return 22; }});
if(o.x === 22) {
    print("passed");
}