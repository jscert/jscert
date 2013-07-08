open Environment;;
open Reference;;

let toBoolean = function
  | Undefined -> Boolean false
  | Null -> Boolean false
  | Boolean b -> Boolean b
  | Number f -> Boolean (not (f = 0. || f = -0. || f = nan))
  | String s -> Boolean (s <> "")
  | _ -> failwith "toBoolean";;

let toNumber = function
  | Undefined -> Number nan
  | Null -> Number 0.
  | Boolean b -> Number (if b then 1. else 0.)
  | Number f -> Number f
  | String s -> Number (try float_of_string s with Failure "float_of_string" -> nan)
  | _ -> failwith "toNumber";;

let toString = function
  | Undefined -> String "undefined"
  | Null -> String "null"
  | Boolean b -> String (string_of_bool b)
  | Number f -> String (string_of_float f)
  | String s -> String s
  | _ -> failwith "toString";;
