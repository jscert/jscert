// First we illustrate copying by value
var n = 1;  // Variable n holds the value 1
var m = n;  // Copy by value: variable m holds a distinct value 1

// Here's a function we'll use to illustrate passing by value
// As we'll see, the function doesn't work the way we'd like it to
add_to_total = function (total, x)
{
    total = total + x;  // This line changes only the internal copy of total
}

// Now call the function, passing the numbers contained in n and m by value.
// The value of n is copied, and that copied value is named total within the
// function. The function adds a copy of m to that copy of n. But adding
// something to a copy of n doesn't affect the original value of n outside
// of the function. So calling this function doesn't accomplish anything.
add_to_total(n, m);

// Now, we'll look at comparison by value.
// In the following line of code, the literal 1 is clearly a distinct numeric
// value encoded in the program. We compare it to the value held in variable
// n. In comparison by value, the bytes of the two numbers are checked to
// see if they are the same.
if (n === 1) { m = 2; }  // n contains the same value as the literal 1; m is now 2
