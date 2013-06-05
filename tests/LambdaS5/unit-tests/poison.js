/**
 * @path ch13/13.2/S13.2.3_A1.js
 * @description check that all poisoning use the [[ThrowTypeError]]
 * function object.
 * @onlyStrict
 */

"use strict";
var poison = Object.getOwnPropertyDescriptor(function() {}, 'caller').get;

if (typeof poison !== 'function') {
  throw("#1: A strict function's .caller should be poisoned with a function");
}
var threw = null;
try {
  poison();
} catch (err) {
  threw = err;
}
if (!threw || !(threw instanceof TypeError)) {
  throw("#2: Poisoned property should throw TypeError");
}

function checkPoison(obj, name) {
  var desc = Object.getOwnPropertyDescriptor(obj, name);
  if (desc.enumerable) {
    throw("#3: Poisoned " + name + " should not be enumerable");
  }
  if (desc.configurable) {
    throw("#4: Poisoned " + name + " should not be configurable");
  }
  if (poison !== desc.get) {
    throw("#5: " + name + "'s getter not poisoned with same poison");
  }
  if (poison !== desc.set) {
    throw("#6: " + name + "'s setter not poisoned with same poison");
  }
}

checkPoison(function() {}, 'caller');
checkPoison(function() {}, 'arguments');
checkPoison((function() { return arguments; })(), 'caller');
checkPoison((function() { return arguments; })(), 'callee');
checkPoison((function() {}).bind(null), 'caller');
checkPoison((function() {}).bind(null), 'arguments');

console.log('passed');
