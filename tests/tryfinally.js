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
    $ERROR('#1: (try {3} finally {4}) !== 3')
}

//////////////////////////////////////////////////////////////////////////////
//CHECK#2
if (eval("while(true){try {3; break} finally {4}}") !== 3) {
    $ERROR('#2: (while(true){try {3; break} finally {4}}) !== 3')
}

//////////////////////////////////////////////////////////////////////////////
//CHECK#3
if (eval("while(true){try {3} finally {4; break}}") !== 3) {
    $ERROR('#3: (while(true){try {3} finally {4; break}}) !== 4')
}

//////////////////////////////////////////////////////////////////////////////
//CHECK#4
if (eval("while(true){try {3; break} finally {4; break}}") !== 3) {
    $ERROR('#4: (while(true){try {3; break} finally {4; break}}) !== 4')
}

