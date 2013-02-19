open Parser_syntax
open List

exception CoqSyntaxDoesNotSupport of string
exception Empty_list

let split_last stmts = (* I think that now this function is useless. -- Martin. *)
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
      | Positive -> Interpreter.Unary_op_add
      | Negative -> Interpreter.Unary_op_neg
      | Pre_Decr -> Interpreter.Unary_op_pre_decr
      | Post_Decr -> Interpreter.Unary_op_post_decr
      | Pre_Incr -> Interpreter.Unary_op_pre_incr
      | Post_Incr -> Interpreter.Unary_op_post_incr
      | Bitnot -> Interpreter.Unary_op_bitwise_not
      | Void -> Interpreter.Unary_op_void

let arith_op_to_coq op : Interpreter.binary_op =
  begin match op with
    | Plus -> Interpreter.Binary_op_add
    | Minus -> Interpreter.Binary_op_sub
    | Times -> Interpreter.Binary_op_mult
    | Div -> Interpreter.Binary_op_div
    | Mod -> Interpreter.Binary_op_mult
    | Bitand -> Interpreter.Binary_op_bitwise_and
    | Bitor -> Interpreter.Binary_op_bitwise_or
    | Bitxor -> Interpreter.Binary_op_bitwise_xor
    | Ursh -> Interpreter.Binary_op_unsigned_right_shift
    | Lsh -> Interpreter.Binary_op_left_shift
    | Rsh -> Interpreter.Binary_op_right_shift
  end

let bin_op_to_coq op : Interpreter.binary_op =
  match op with
    | Comparison op ->
      begin match op with
              | Lt -> Interpreter.Binary_op_lt
              | Le -> Interpreter.Binary_op_le
              | Gt -> Interpreter.Binary_op_gt
              | Ge -> Interpreter.Binary_op_ge
              | Equal -> Interpreter.Binary_op_equal
              | NotEqual -> Interpreter.Binary_op_disequal
              | TripleEqual -> Interpreter.Binary_op_strict_equal
              | NotTripleEqual -> Interpreter.Binary_op_strict_disequal
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
      | Var v -> Interpreter.Expr_identifier (string_to_coq v)
      | Delete e -> Interpreter.Expr_unary_op (Interpreter.Unary_op_delete, f e)
      | Access (e, v) -> Interpreter.Expr_member (f e, string_to_coq v)
      | Unary_op (op, e) -> Interpreter.Expr_unary_op (unary_op_to_coq op, f e)
      | BinOp (e1, op, e2) -> Interpreter.Expr_binary_op (f e1, bin_op_to_coq op, f e2)
      | Assign (e1, e2)  -> Interpreter.Expr_assign (f e1, None, f e2)
      | AssignOp (e1, op, e2) -> Interpreter.Expr_assign (f e1, Some (arith_op_to_coq op), f e2)
      | CAccess (e1, e2) -> Interpreter.Expr_access (f e1, f e2)
      | Comma (e1, e2) -> Interpreter.Expr_binary_op (f e1, Interpreter.Binary_op_coma, f e2)
      | Call (e1, e2s) -> Interpreter.Expr_call (f e1, map (fun e2 -> f e2) e2s)
      | New (e1, e2s) -> Interpreter.Expr_new (f e1, map (fun e2 -> f e2) e2s)
      | AnnonymousFun (s, vs, e) -> Interpreter.Expr_function (None, (map string_to_coq vs), exp_to_funcbody e s)
      | NamedFun (s, n, vs, e) -> Interpreter.Expr_function (Some (string_to_coq n), (map string_to_coq vs), exp_to_funcbody e s)
      | Obj xs -> Interpreter.Expr_object (map (fun (s,e) -> Interpreter.Propname_string (string_to_coq s), Interpreter.Propbody_val (f e)) xs)
      | Array _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | ConditionalOp (e1, e2, e3) -> Interpreter.Expr_conditional (f e1, f e2, f e3)

      (*Statements*)
      | Skip 
      | Return _
      | Break _ 
      | Continue _ 
      | Debugger  
      | VarDec _ 
      | Throw _  
      | Label _
      | While _
      | DoWhile _
      | With _
      | Try _
      | If _
      | ForIn _
      | For _
      | Switch _ 
      | Block _ 
      | Script _ -> raise Parser.InvalidArgument

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
      | Obj _
      | Array _ 
      | ConditionalOp _ -> Interpreter.Stat_expr (exp_to_exp exp)

      | AnnonymousFun _
      | NamedFun _ -> raise Parser.InvalidArgument (* If a function appears in the middle of a statement, it shall not be interpreted as an expression function, but as a function declaration and thus be rejected by the parser. *)
	  (* I'm afraid I don't understand the code in `tests/sputnik/tests/Conformance/12_Statement/12.10_The_with_Statement/S12.10_A3.3_T4.js' that precisely declares a function in the middle of a statement. -- Martin *)

      (*Statements*)
	  | Skip -> Interpreter.Stat_block []
      | Return (Some e) -> Interpreter.Stat_return (Some (exp_to_exp e))
      | Return None -> Interpreter.Stat_return None
      | Break (Some l) -> Interpreter.Stat_break (Some (string_to_coq l))
      | Break None -> Interpreter.Stat_break None
      | Continue (Some l) -> Interpreter.Stat_continue (Some (string_to_coq l))
      | Continue None -> Interpreter.Stat_continue None
      | Debugger -> Interpreter.Stat_debugger
      | VarDec vs -> Interpreter.Stat_var_decl (map (fun (v, e) ->
          string_to_coq v, match e with None -> None | Some e -> Some (exp_to_exp e)) vs)
      | Throw e -> Interpreter.Stat_throw (exp_to_exp e)
      | Label (l, e) -> Interpreter.Stat_label (string_to_coq l, f e)
      | While (e1, e2)  -> Interpreter.Stat_while (exp_to_exp e1, f e2)
      | DoWhile (e1, e2) -> Interpreter.Stat_do_while (f e1, exp_to_exp e2)
      | With (e1, e2) -> Interpreter.Stat_with (exp_to_exp e1, f e2) 
      | Try (e, None, None) -> Interpreter.Stat_try (f e, None, None)
      | Try (e, None, Some fe) -> Interpreter.Stat_try (f e, None, Some (f fe))
      | Try (e, Some (s, ce), None) -> Interpreter.Stat_try (f e, Some (string_to_coq s, f ce), None)
      | Try (e, Some (s, ce), Some fe) -> Interpreter.Stat_try (f e, Some (string_to_coq s, f ce), Some (f fe))  
      | If (e1, e2, Some e3) -> Interpreter.Stat_if (exp_to_exp e1, f e2, Some (f e3))
      | If (e1, e2, None) -> Interpreter.Stat_if (exp_to_exp e1, f e2, None)
      | ForIn (e1, e2, e3) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp)) (* TODO:  We could actually do something there *)
      | For (e1, e2, e3, e4) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Switch (e1, e2s) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | Block es -> Interpreter.Stat_block (List.map f es)

      | Script _ -> raise Parser.InvalidArgument

and exp_to_prog exp : Interpreter.prog =
  match exp.exp_stx with
    | Script (s, e2s) -> Interpreter.Prog_intro (s, map exp_to_elem e2s)
    | Block (e2s) -> Interpreter.Prog_intro (false, map exp_to_elem e2s)
    | _ ->  Interpreter.Prog_intro (false, [exp_to_elem exp])

and exp_to_elem exp : Interpreter.element = 
    let tos = string_to_coq in
    match exp.exp_stx with
      | NamedFun (s, name, args, body) -> Interpreter.Element_func_decl (tos name, map tos args, exp_to_funcbody body s)
      | _ -> Interpreter.Element_stat (exp_to_stat exp)
  
and exp_to_funcbody exp strict : Interpreter.funcbody =
  let body = match exp_to_prog exp with
    | Interpreter.Prog_intro (_, elems) -> Interpreter.Prog_intro (strict, elems) in
  Interpreter.Funcbody_intro (body, [])

let coq_syntax_from_file filename =
  let exp = Parser_main.exp_from_file filename in
  exp_to_prog exp
  
let coq_syntax_from_string s =
  let exp = Parser_main.exp_from_string s in
  exp_to_prog exp

