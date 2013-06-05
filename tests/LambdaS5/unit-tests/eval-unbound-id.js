try {
  eval("'use strict';x");
}
catch (e) {
  if (e instanceof ReferenceError) {
    console.log('Passed');
  }
}
