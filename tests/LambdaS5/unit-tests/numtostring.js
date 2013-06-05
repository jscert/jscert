var a = new Number(0);
var b = new Number(-33);
var c = new Number(400);
var d = new Number(687.554221);
var e = new Number(-87467815.333);
var f = new Number(64);

if (a.toString() === "0") {
  if (b.toString() === "-33") {
    if (c.toString() === "400") {
      if (d.toString() === "687.554221") {
        if (e.toString() === "-87467815.333") {
          if (f.toString(16) === "40") {
            if (b.toString(3) === "-1020" &&
                b.toString(7) === "-45" &&
                b.toString(29) === "-14") {
              print("passed");
            }
          }
        }
      }
    }
  }
}
