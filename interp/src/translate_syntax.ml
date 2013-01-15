open Parser_syntax
open List

exception CoqSyntaxDoesNotSupport of string
exception Empty_list

let split_last stmts = 
  match stmts with
    | [] -> raise Empty_list 
    | hd :: tl ->
      let rec aux l acc = function
          | [] -> l, rev acc
          | hd :: tl -> aux hd (l::acc) tl
      in aux hd [] tl

let string_to_coq s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  rev !l
  
let unary_op_to_coq op : Interpreter.unary_op =
  match op with
      | Not -> Interpreter.Unary_op_not
      | TypeOf -> Interpreter.Unary_op_typeof
      | Positive
      | Negative -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_unary_op op))
      | Pre_Decr -> Interpreter.Unary_op_pre_decr
      | Post_Decr -> Interpreter.Unary_op_post_decr
      | Pre_Incr -> Interpreter.Unary_op_pre_incr
      | Post_Incr -> Interpreter.Unary_op_post_incr
      | Bitnot -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_unary_op op))
      | Void -> Interpreter.Unary_op_void

let arith_op_to_coq op : Interpreter.binary_op =
  begin match op with
    | Plus -> Interpreter.Binary_op_add
	  | Minus -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_arith_op op))
	  | Times -> Interpreter.Binary_op_mult
	  | Div -> Interpreter.Binary_op_div
	  | Mod 
	  | Ursh
	  | Lsh
	  | Rsh
	  | Bitand
	  | Bitor
	  | Bitxor -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_arith_op op))
  end

let bin_op_to_coq op : Interpreter.binary_op =
  match op with
    | Comparison op ->
      begin match op with
              | Equal -> Interpreter.Binary_op_equal
              | NotEqual
              | TripleEqual 
              | NotTripleEqual
              | Lt 
              | Le
              | Gt
              | Ge -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_comparison_op op))
              | In -> Interpreter.Binary_op_in
              | InstanceOf -> Interpreter.Binary_op_instanceof
      end
    | Arith op -> arith_op_to_coq op
    | Boolean op ->
      begin match op with
        | And -> Interpreter.Binary_op_and
        | Or -> Interpreter.Binary_op_or
      end
  
let exp_to_literal exp : Interpreter.literal =
  match exp.exp_stx with
      | Num n -> Interpreter.Literal_number n
      | String s -> Interpreter.Literal_string (string_to_coq s)
      | Null -> Interpreter.Literal_null 
      | Bool b -> Interpreter.Literal_bool b
      | _ -> raise Parser.InvalidArgument

let rec exp_to_exp exp : Interpreter.expr =
  let f = exp_to_exp in 
  match exp.exp_stx with
      (* Literals *)
      | Num _
      | String _ 
      | Null 
      | Bool _ -> Interpreter.Expr_literal (exp_to_literal exp)
      
      | RegExp _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | This -> Interpreter.Expr_this
      | Var v -> Interpreter.Expr_variable (string_to_coq v)
      | Delete e -> Interpreter.Expr_unary_op (Interpreter.Unary_op_delete, f e)
      | Access (e, v) -> Interpreter.Expr_member (f e, string_to_coq v)
      | Unary_op (op, e) -> Interpreter.Expr_unary_op (unary_op_to_coq op, f e)
      | BinOp (e1, op, e2) -> Interpreter.Expr_binary_op (f e1, bin_op_to_coq op, f e2)
      | Assign (e1, e2)  -> Interpreter.Expr_assign (f e1, None, f e2)
      | AssignOp (e1, op, e2) -> Interpreter.Expr_assign (f e1, Some (arith_op_to_coq op), f e2)
      | CAccess (e1, e2) -> Interpreter.Expr_access (f e1, f e2)
      | Comma (e1, e2) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Call (e1, e2s) -> Interpreter.Expr_call (f e1, map (fun e2 -> f e2) e2s)
      | New (e1, e2s) -> Interpreter.Expr_new (f e1, map (fun e2 -> f e2) e2s)
      | AnnonymousFun (vs, e) -> Interpreter.Expr_function (None, (map string_to_coq vs), exp_to_prog e)
      | NamedFun (n, vs, e) -> Interpreter.Expr_function 
        (Some (string_to_coq n), (map string_to_coq vs), exp_to_prog e)
      | Obj xs -> Interpreter.Expr_object (map (fun (s,e) -> Interpreter.Propname_string (string_to_coq s), Interpreter.Propbody_val (f e)) xs)
      | Array _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | ConditionalOp _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))

      (*Statements*)
      | Skip 
      | Return _
      | Break _ 
      | Continue _ 
      | Debugger  
      | VarDec _ 
      | Throw _  
      | Label _
      | Seq _
      | While _
      | With _
      | Try _
      | If _
      | ForIn _
      | Switch _ 
      | Block _ -> raise Parser.InvalidArgument

and exp_to_stat exp : Interpreter.stat =
  let f = exp_to_stat in 
  match exp.exp_stx with
        (* Literals *)
      | Num _
      | String _
      | Null 
      | Bool _
      
      (* Expressions *)
      | RegExp _  
      | This
      | Var _
      | Delete _ 
      | Access _
      | Unary_op _ 
      | BinOp _ 
      | Assign _  
      | AssignOp _
      | CAccess _
      | Comma _
      | Call _
      | New _
      | AnnonymousFun _
      | NamedFun _ 
      | Obj _
      | Array _ 
      | ConditionalOp _ -> Interpreter.Stat_expr (exp_to_exp exp)

      (*Statements*)
      | Skip -> Interpreter.Stat_skip
      | Return (Some e) -> f e
      | Return None -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp)) (* Note:  Now it accepts this. -- Martin *)
      | Break _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Continue _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Debugger -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | VarDec (v, None) -> Interpreter.Stat_var_decl [string_to_coq v, None]
      | VarDec (v, Some e) -> Interpreter.Stat_var_decl [string_to_coq v, Some (exp_to_exp e)]
      | Throw e -> Interpreter.Stat_throw (exp_to_exp e)
      | Label (_, e) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))   
      | Seq (e1, e2) -> Interpreter.Stat_seq (f e1, f e2)
      | While (e1, e2)  -> Interpreter.Stat_while (exp_to_exp e1, f e2)
      | With (e1, e2) -> Interpreter.Stat_with (exp_to_exp e1, f e2) 
      | Try (e, None, None) -> Interpreter.Stat_try (f e, None, None)
      | Try (e, None, Some fe) -> Interpreter.Stat_try (f e, None, Some (f fe))
      | Try (e, Some (s, ce), None) -> Interpreter.Stat_try (f e, Some (string_to_coq s, f ce), None)
      | Try (e, Some (s, ce), Some fe) -> Interpreter.Stat_try (f e, Some (string_to_coq s, f ce), Some (f fe))  
      | If (e1, e2, Some e3) -> Interpreter.Stat_if (exp_to_exp e1, f e2, Some (f e3))
      | If (e1, e2, None) -> Interpreter.Stat_if (exp_to_exp e1, f e2, None)
      | ForIn (e1, e2, e3) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Switch (e1, e2s) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Block es -> 
        begin match es with
	        | [] -> Interpreter.Stat_skip
	        | stmts ->
             let last, stmts = split_last stmts in
	           List.fold_right (fun s1 s2 -> Interpreter.Stat_seq (f s1, s2)) stmts (f last)
        end

and exp_to_prog exp =
  let f = exp_to_prog in
  let tos = string_to_coq in
  match exp.exp_stx with
	  | NamedFun (name, args, body) -> 
      Interpreter.Prog_function_decl (tos name, map tos args, f body)
	  | Seq (e1, e2) -> Interpreter.Prog_seq (f e1, f e2)
	  | _ -> Interpreter.Prog_stat (exp_to_stat exp)

let coq_syntax_from_file filename =
  let exp = Parser_main.exp_from_file filename in
  exp_to_prog exp
  
let coq_syntax_from_string s =
  let exp = Parser_main.exp_from_string s in
  exp_to_prog exp

