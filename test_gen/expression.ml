open Environment;;
open Reference;;
open Conversion;;

type literals = NullLiteral
              | BooleanLiteral of bool
              | NumericLiteral of float
              | StringLiteral of string
              | RegularExpressionLiteral;;

type primary = This
             | Identifier
             | Literal of literals
             | ArrayLiteral
             | ObjectLiteral
             | Expression;;

type t = Primary of primary
       | LeftHandSide
       | PostFix
       | UnaryOperators
       | MultiplicativeOperators
       | AdditiveOperators
       | BitwiseOperators
       | RelationalOperators
       | EqualityOperators;;


let eval env =

  let primary = function
    | Literal l -> begin match l with
        | NullLiteral -> Null
        | BooleanLiteral b -> Boolean b
        | NumericLiteral f -> Number f
        | StringLiteral s -> String s
        | RegularExpressionLiteral -> failwith "RegularExpressionLiteral not yet implemented"
      end
    | _ -> failwith "PrimaryExpression not yet implemented"
    
  in
    let expression = function
      | Primary pe -> Value (primary pe)
      | _ -> failwith "Expression not yet implemented"

in
  expression;;


(* Generator *)

module type GeneratorSig =
sig
  
  class generator :
  object
  
    method expression : t
    method expression_true : t
    method expression_false : t
  
  end

end;;

module Generator : GeneratorSig =
struct

  let random_string () =
    let alphabet = [|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l";
           "m"; "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"|] in
      alphabet.(Random.int 26) ^ alphabet.(Random.int 26) ^
      alphabet.(Random.int 26) ^ alphabet.(Random.int 26);;
  
  let literals_true () = match Random.int 3 with
    | 0 -> BooleanLiteral true
    | 1 -> NumericLiteral (1. +. floor (Random.float 9.))
    | _ -> StringLiteral (random_string ())  
  
  let literals_false () = match Random.int 3 with
    | 0 -> BooleanLiteral false
    | 1 -> NumericLiteral (if Random.bool () then  0. else nan)
    | _ -> StringLiteral ""

  let literals () = match Random.int 4 with
    | 0 -> NullLiteral
    | 1 -> BooleanLiteral (Random.bool ())
    | 2 -> NumericLiteral (floor (Random.float 10.))
    | 3 -> StringLiteral (random_string ())
    | _ -> RegularExpressionLiteral

  let primary = function 
    | 0 -> This
    | 1 -> Identifier
    | 2 -> Literal (literals ())
    | 3 -> ArrayLiteral
    | 4 -> ObjectLiteral
    | _ -> Expression;;

  let expression = function
    | 0 -> Primary (primary 2)
    | 1 -> LeftHandSide
    | 2 -> PostFix
    | 3 -> UnaryOperators
    | 4 -> MultiplicativeOperators
    | 5 -> AdditiveOperators
    | 6 -> BitwiseOperators
    | 7 -> RelationalOperators
    | _ -> EqualityOperators;;

  let expression_true () = Primary (Literal (literals_true ()));;

  let expression_false () = Primary (Literal (literals_false ()));;

  class generator =
  object

    method expression = expression 0
    method expression_true = expression_true ()
    method expression_false = expression_false ()

  end

end;;

let create () = new Generator.generator;;
