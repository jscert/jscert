// Copyright 2013 JScert, but we can give it away ;-)
// Changelog: initial test by Alan Schmitt

/**
* @name: tofill;
* @section: 12.14;
* @assertion: TryStatement : try Block Finally returns the result of the Block if the result of the Finally is normal;
* @description: tofill;
*/

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (eval("try {3} finally {4}") !== 3) {
    $ERROR('#1: (try {3} finally {4} !== 3)')
}
