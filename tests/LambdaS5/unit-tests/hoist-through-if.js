// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * FunctionDeclaration cannot be localed inside an Expression
 *
 * @section 14
 * @path 14_Program/S14_A2.js
 * @description Declaring a function within an "if" Expression
 */

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (typeof f !== 'undefined') {
	throw('#1: typeof f === \'undefined\'. Actual:  typeof f ==='+ typeof f  );
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#2
if (function f(arg){
	if (arg===0)
	   return 1;
	else
	   return f(arg-1)*arg;
}(3)!==6) {
	throw('#2: FunctionDeclaration cannot be localed inside an Expression');
};
console.log('passed');
//
//////////////////////////////////////////////////////////////////////////////

