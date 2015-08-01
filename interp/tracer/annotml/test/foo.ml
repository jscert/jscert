let f x = x + 1 in
let res = List.map string_of_int [1;2;3] in
f (Bar.g 2)
