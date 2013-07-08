open Environment;;
open Reference;;
open Expression;;
open Statement;;

let tb = "|  ";;


(* Types *)

let literals tab = function
  | NullLiteral -> "NullLiteral"
  | BooleanLiteral b -> Printf.sprintf "BooleanLiteral %s" (if b then "true" else "false")
  | NumericLiteral f -> Printf.sprintf "NumericLiteral %f" f
  | StringLiteral s -> Printf.sprintf "StringLiteral %s" s
  | RegularExpressionLiteral -> "RegularExpressionLiteral";;

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

let result res = Printf.sprintf "{rtype : %s; rvalue : %s; rtarget : %s}"
  (rtype res.rtype) (rvalue res.rvalue) (rtarget res.rtarget);;



(* Expression *)

let expression tab e =

  let primary = function
    | This -> "This"
    | Identifier -> "Identifier"
    | Literal l -> Printf.sprintf "Literal %s" (literals tab l)
    | ArrayLiteral -> "ArrayLiteral"
    | ObjectLiteral -> "ObjectLiteral"
    | Expression -> "Expression"
  
  in match e with
    | Primary p -> Printf.sprintf "%sPrimary %s" tab (primary p)
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
  | s :: l -> Printf.sprintf "%s\n%s" (statement (tab ^ tb) s) (block tab l)

and variable_statement tab = function
  | [] -> tab
  | v :: l -> begin match v with
      | VariableIdentifier r -> Printf.sprintf "%sVariableIdentifier %s" tab r
      | VariableInitialiser (r, e) -> Printf.sprintf "%sVariableInitialiser %s ->\n%s" tab r (expression (tab ^ tb) e)
    end

and if_statement tab = function
  | IfThen (e, s) -> Printf.sprintf "%sIf\n%s\n%sThen\n%s"
      tab (expression (tab ^ tb) e) tab (statement (tab ^ tb) s)
  | IfThenElse (e, s1, s2) ->Printf.sprintf "%sIf\n%s\n%sThen\n%s\n%sElse\n%s"
      tab (expression (tab ^ tb) e) tab (statement (tab ^ tb) s1) tab (statement (tab ^ tb) s2)

and continue_statement = function
  | ContinueEmpty -> "Empty"
  | ContinueIdentifier i -> rtarget i

and break_statement = function
  | BreakEmpty -> "Empty"
  | BreakIdentifier i -> rtarget i

and return_statement tab = function
  | ReturnEmpty -> "Empty"
  | ReturnExpression e -> (expression (tab ^ tb) e)

and try_statement tab = function 
  | TryBlockCatch -> "TryBLockCatch"
  | TryBlockFinally (b, f) -> Printf.sprintf "%sTryBlockFinally\n%sBlock\n%s\n%sFinally\n%s"
      tab (tab ^ tb) (block (tab ^ tb) b) (tab ^ tb) (block (tab ^ tb) f)
  | TryBlockCatchFinally -> "TryBlockCatchFinally"

and statement tab = function
  | Block b -> Printf.sprintf "%sBlock\n%s" tab (block tab b)
  | VariableStatement v -> Printf.sprintf "%sVariableStatement\n%s"
      tab (variable_statement (tab ^ tb) v)
  | EmptyStatement -> Printf.sprintf "%sEmptyStatement" tab
  | ExpressionStatement e -> Printf.sprintf "%sExpressionStatement\n%s"
      tab (expression (tab ^ tb) e)
  | IfStatement t -> Printf.sprintf "%sIfStatement\n%s" tab (if_statement (tab ^ tb) t)
  | IterationStatement -> "IterationStatement"
  | ContinueStatement t -> Printf.sprintf  "%sContinueStatement %s" tab (continue_statement t)
  | BreakStatement t -> Printf.sprintf  "%sBreakStatement %s" tab (break_statement t)
  | ReturnStatement t -> Printf.sprintf "%sReturnStatement\n%s" tab (return_statement (tab ^ tb) t)
  | WithStatement -> "WithStatement"
  | LabelledStatement (s, t) -> Printf.sprintf "%sLabelledStatement %s\n%s"
      tab s (statement (tab ^ tb) t)
  | SwitchStatement -> "SwitchStatement"
  | ThrowStatement e -> Printf.sprintf "%sThrowStatement\n%s" tab (expression (tab ^ tb) e)
  | TryStatement t -> Printf.sprintf "%sTryStatement\n%s" tab (try_statement (tab ^ tb) t)
  | DebuggerStatement -> "DebuggerStatement";;
