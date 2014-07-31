/*
* Tentative redefinitions of InstallFunctions and SetUpLockedPrototype
* These functions make assumptions about lack of redefinition of certain ch15 functions
*/


// Helper function used to install functions on objects.
function InstallFunctions(object, attributes, functions) {
  for (var i = 0; i < functions.length; i+=2) {
    var key = functions[i];
    var f = functions[i + 1];
    f.prototype = undefined;
    var read_only = Boolean(attributes & 1);
    var dont_enum = Boolean(attributes & 2);
    var dont_delete = Boolean(attributes & 4);
    object[key] = f;
    var descriptor = {writable: !read_only,
                      enumerable: !dont_enum,
                      configurable: !dont_delete
                     };
    Object.defineProperty(object, key, descriptor);
  }
}


// Prevents changes to the prototype of a built-in function.
// The "prototype" property of the function object is made non-configurable,
// and the prototype object is made non-extensible.

//as an aside. I've tried to stick as close to the effects of the V8 version
//even when I'm not sure it's necessary for our purposes
function SetUpLockedPrototype(constructor, fields, methods) {
  var prototype = constructor.prototype;
  if (fields) {
    for (var i = 0; i < fields.length; i++) {
      prototype[fields[i]] = undefined;
      Object.defineProperty(prototype, fields[i],
                            {enumerable: false, configurable: false});
    }
  for (var i = 0; i < methods.length; i += 2) {
    var key = methods[i];
    var f = methods[i + 1];
    prototype[key] = f;
    Object.defineProperty(prototype, key, 
                         {writable: false, enumerable: false, configurable: false});
  }
  prototype.prototype = null;
}