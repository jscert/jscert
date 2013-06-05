"use strict";

try {
  x = 3;
} catch (e) {
  if (e instanceof ReferenceError) {
    print("passed");
  }
}
