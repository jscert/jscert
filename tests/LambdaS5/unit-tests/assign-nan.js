"use strict";
try {
  NaN = 100;
} catch(e) {
  if(e instanceof TypeError) {
    console.log('passed');
  }
}

