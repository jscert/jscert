open Environment;;
open Reference;;
open Expression;;
open Statement;;

let tb = " ";;


(* Types *)

let literals tab = function
  | NullLiteral -> "null"
  | BooleanLiteral b -> string_of_bool b
  | NumericLiteral f -> string_of_float f
  | StringLiteral s -> "\034" ^ s ^ "\034"
  | RegularExpressionLiteral -> "null";;

let primary = function
  | Undefined -> "Undefined"
  | Null -> "Null"
  | Boolean b -> Printf.sprintf "Boolean %s" (if b then "true" else "false")
  | Number f -> Printf.sprintf "Number %f" f
  | String s -> Printf.sprintf "String %s" s
  | _ -> failwith "primary";;

let rtype = function
  | Normal -> "Normal"
  | Break -> "Break"
  | Continue -> "Continue"
  | Return -> "Return"
  | Throw -> "Throw";;
  
let rvalue = function
  | EmptyValue -> "EmptyValue"
  | Value p -> Printf.sprintf "Value %s" (primary p)
  | Reference r -> Printf.sprintf "Reference %s" r.name;;

let rtarget = function
  | Ident s -> Printf.sprintf "Ident %s" s
  | EmptyTarget -> "EmptyTarget";;

(* Expressions *)

let expression tab e =

  let primary = function
    | This -> "This"
    | Identifier -> "Identifier"
    | Literal l -> (literals tab l)
    | ArrayLiteral -> "ArrayLiteral"
    | ObjectLiteral -> "ObjectLiteral"
    | Expression -> "Expression"
  
  in match e with
    | Primary p -> primary p
    | LeftHandSide -> "LeftHandSide"
    | PostFix -> "PostFix"
    | UnaryOperators -> "UnaryOperators"
    | MultiplicativeOperators -> "MultiplicativeOperators"
    | AdditiveOperators -> "AdditiveOperators"
    | BitwiseOperators -> "BitwiseOperators"
    | RelationalOperators -> "RelationalOperators"
    | EqualityOperators -> "EqualityOperators";;


(* Statement *)

let rec block tab = function
  | [] -> tab
  | s :: l -> Printf.sprintf "%s;\n%s" (statement (tab ^ tb) s) (block tab l)

and variable tab = function
  | [] -> ""
  | [v] -> begin match v with
      | VariableIdentifier r -> r
      | VariableInitialiser (r, e) -> Printf.sprintf "%s = %s" r (expression tab e)
    end
  | v :: l -> begin match v with
      | VariableIdentifier r -> Printf.sprintf "%s, %s" r (variable tab l)
      | VariableInitialiser (r, e) -> Printf.sprintf "%s = %s, %s" r (expression tab e) (variable tab l)
    end

and if_statement tab = function
  | IfThen (e, s) -> Printf.sprintf "%sif (%s) {\n%s;\n%s}"
      tab (expression (tab ^ tb) e) (statement (tab ^ tb) s) tab
  | IfThenElse (e, s1, s2) -> Printf.sprintf "%sif (%s) {\n%s;\n%s}\n%selse {\n%s;\n%s}"
      tab (expression (tab ^ tb) e) tab (statement (tab ^ tb) s1) tab (statement (tab ^ tb) s2) tab

and continue_statement = function
  | ContinueEmpty -> ""
  | ContinueIdentifier i -> rtarget i

and break_statement = function
  | BreakEmpty -> ""
  | BreakIdentifier i -> rtarget i

and return_statement tab = function
  | ReturnEmpty -> ""
  | ReturnExpression e -> (expression (tab ^ tb) e)

and try_statement tab = function 
  | TryBlockCatch -> "TryBLockCatch"
  | TryBlockFinally (b, f) -> Printf.sprintf "%stry {\n%s;\n%s}\n%sfinally {\n%s;\n%s}"
      tab (block (tab ^ tb) b) tab tab (block (tab ^ tb) f) tab
  | TryBlockCatchFinally -> "TryBlockCatchFinally"

and statement tab = function
  | Block b -> Printf.sprintf "%s{\n%s%s}" tab (block tab b) tab
  | VariableStatement v -> Printf.sprintf "%svar %s" tab (variable tab v)
  | EmptyStatement -> Printf.sprintf "%s;" tab
  | ExpressionStatement e -> Printf.sprintf "%s%s" tab (expression (tab ^ tb) e)
  | IfStatement t ->  (if_statement (tab ^ tb) t)
  | IterationStatement -> "IterationStatement"
  | ContinueStatement t -> (continue_statement t)
  | BreakStatement t -> Printf.sprintf  "%sbreak %s;" tab (break_statement t)
  | ReturnStatement t -> Printf.sprintf "%sreturn %s;" tab (return_statement (tab ^ tb) t)
  | WithStatement -> "WithStatement"
  | LabelledStatement (s, t) -> "LabelledStatement"
  | SwitchStatement -> "SwitchStatement"
  | ThrowStatement e -> Printf.sprintf "%sthrow %s" tab (expression (tab ^ tb) e)
  | TryStatement t -> (try_statement (tab ^ tb) t)
  | DebuggerStatement -> "DebuggerStatement";;

let result res = Printf.sprintf "//{type = %s; value = %s; target = %s}"
  (rtype res.rtype) (rvalue res.rvalue) (rtarget res.rtarget);;
