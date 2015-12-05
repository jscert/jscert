open Fappli_IEEE_bits
open JsNumber
open Parser_syntax
open List

exception CoqSyntaxDoesNotSupport of string
exception Empty_list

let string_to_coq s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  rev !l
  
let unary_op_to_coq op : JsSyntax.unary_op =
  match op with
      | Not -> JsSyntax.Coq_unary_op_not
      | TypeOf -> JsSyntax.Coq_unary_op_typeof
      | Positive -> JsSyntax.Coq_unary_op_add
      | Negative -> JsSyntax.Coq_unary_op_neg
      | Pre_Decr -> JsSyntax.Coq_unary_op_pre_decr
      | Post_Decr -> JsSyntax.Coq_unary_op_post_decr
      | Pre_Incr -> JsSyntax.Coq_unary_op_pre_incr
      | Post_Incr -> JsSyntax.Coq_unary_op_post_incr
      | Bitnot -> JsSyntax.Coq_unary_op_bitwise_not
      | Void -> JsSyntax.Coq_unary_op_void

let arith_op_to_coq op : JsSyntax.binary_op =
  begin match op with
    | Plus -> JsSyntax.Coq_binary_op_add
    | Minus -> JsSyntax.Coq_binary_op_sub
    | Times -> JsSyntax.Coq_binary_op_mult
    | Div -> JsSyntax.Coq_binary_op_div
    | Mod -> JsSyntax.Coq_binary_op_mod
    | Bitand -> JsSyntax.Coq_binary_op_bitwise_and
    | Bitor -> JsSyntax.Coq_binary_op_bitwise_or
    | Bitxor -> JsSyntax.Coq_binary_op_bitwise_xor
    | Ursh -> JsSyntax.Coq_binary_op_unsigned_right_shift
    | Lsh -> JsSyntax.Coq_binary_op_left_shift
    | Rsh -> JsSyntax.Coq_binary_op_right_shift
  end

let bin_op_to_coq op : JsSyntax.binary_op =
  match op with
    | Comparison op ->
      begin match op with
              | Lt -> JsSyntax.Coq_binary_op_lt
              | Le -> JsSyntax.Coq_binary_op_le
              | Gt -> JsSyntax.Coq_binary_op_gt
              | Ge -> JsSyntax.Coq_binary_op_ge
              | Equal -> JsSyntax.Coq_binary_op_equal
              | NotEqual -> JsSyntax.Coq_binary_op_disequal
              | TripleEqual -> JsSyntax.Coq_binary_op_strict_equal
              | NotTripleEqual -> JsSyntax.Coq_binary_op_strict_disequal
              | In -> JsSyntax.Coq_binary_op_in
              | InstanceOf -> JsSyntax.Coq_binary_op_instanceof
      end
    | Arith op -> arith_op_to_coq op
    | Boolean op ->
      begin match op with
        | And -> JsSyntax.Coq_binary_op_and
        | Or -> JsSyntax.Coq_binary_op_or
      end
  
let exp_to_literal exp : JsSyntax.literal =
  match exp.exp_stx with
      | Num n -> JsSyntax.Coq_literal_number n
      | String s -> JsSyntax.Coq_literal_string (string_to_coq s)
      | Null -> JsSyntax.Coq_literal_null 
      | Bool b -> JsSyntax.Coq_literal_bool b
      | _ -> raise Parser.InvalidArgument

let rec exp_to_exp exp : JsSyntax.expr =
  let f = exp_to_exp in 
  let string_to_coq_op e = match e with 
    | None -> None
    | Some e -> Some (string_to_coq e) in
  match exp.exp_stx with
      (* Literals *)
      | Num _
      | String _ 
      | Null 
      | Bool _ -> JsSyntax.Coq_expr_literal (exp_to_literal exp)

      | RegExp _ -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | This -> JsSyntax.Coq_expr_this
      | Var v -> JsSyntax.Coq_expr_identifier (string_to_coq v)
      | Delete e -> JsSyntax.Coq_expr_unary_op (JsSyntax.Coq_unary_op_delete, f e)
      | Access (e, v) -> JsSyntax.Coq_expr_member (f e, string_to_coq v)
      | Unary_op (op, e) -> JsSyntax.Coq_expr_unary_op (unary_op_to_coq op, f e)
      | BinOp (e1, op, e2) -> JsSyntax.Coq_expr_binary_op (f e1, bin_op_to_coq op, f e2)
      | Assign (e1, e2)  -> JsSyntax.Coq_expr_assign (f e1, None, f e2)
      | AssignOp (e1, op, e2) -> JsSyntax.Coq_expr_assign (f e1, Some (arith_op_to_coq op), f e2)
      | CAccess (e1, e2) -> JsSyntax.Coq_expr_access (f e1, f e2)
      | Comma (e1, e2) -> JsSyntax.Coq_expr_binary_op (f e1, JsSyntax.Coq_binary_op_coma, f e2)
      | Call (e1, e2s) -> JsSyntax.Coq_expr_call (f e1, map (fun e2 -> f e2) e2s)
      | New (e1, e2s) -> JsSyntax.Coq_expr_new (f e1, map (fun e2 -> f e2) e2s)
      | FunctionExp (s, n, vs, e) -> JsSyntax.Coq_expr_function ((string_to_coq_op n), (map string_to_coq vs), exp_to_funcbody e s)
      | Function (s, n, vs, e) -> JsSyntax.Coq_expr_function ((string_to_coq_op n), (map string_to_coq vs), exp_to_funcbody e s)
      | Obj xs -> JsSyntax.Coq_expr_object (map (fun (pn,p,e) -> 
        (match pn with 
          | PropnameId id -> JsSyntax.Coq_propname_identifier (string_to_coq id)
          | PropnameString s -> JsSyntax.Coq_propname_string (string_to_coq s)
          | PropnameNum n -> JsSyntax.Coq_propname_number n
        ),
        (match p with
          | PropbodyVal -> JsSyntax.Coq_propbody_val (f e)
          | PropbodyGet -> 
            begin match e.exp_stx with 
              | FunctionExp (s, None, vs, e) -> JsSyntax.Coq_propbody_get (exp_to_funcbody e s)
              | Function (s, None, vs, e) -> JsSyntax.Coq_propbody_get (exp_to_funcbody e s) 
              | _ -> raise Parser.InvalidArgument
            end
          | PropbodySet ->
            begin match e.exp_stx with
              | FunctionExp (s, None, vs, e) -> JsSyntax.Coq_propbody_set (map string_to_coq vs, exp_to_funcbody e s) 
              | Function (s, None, vs, e) -> JsSyntax.Coq_propbody_set (map string_to_coq vs, exp_to_funcbody e s) 
              | _ -> raise Parser.InvalidArgument
            end) 
        ) xs)
      (* _ARRAYS_ : Parsing array arguments *)
      | Array oes -> JsSyntax.Coq_expr_array (map (fun oe -> begin match oe with
                                                               | None   -> None
                                                               | Some e -> Some (f e)
                                                              end) oes)
      | ConditionalOp (e1, e2, e3) -> JsSyntax.Coq_expr_conditional (f e1, f e2, f e3)

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

and exp_to_stat exp : JsSyntax.stat =
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
      | ConditionalOp _
      | FunctionExp _ -> JsSyntax.Coq_stat_expr (exp_to_exp exp)

      | Function _ -> raise Parser.InvalidArgument
         (* If a function appears in the middle of a statement, it shall not be interpreted as an expression function, but as a function declaration *)
         (* NOTE in spec p.86 *)
         (* ... It is recommended that ECMAScript implementations either disallow this usage of FunctionDeclaration or issue a warning *)

      (*Statements*)
	  | Skip -> JsSyntax.Coq_stat_block []
      | Return (Some e) -> JsSyntax.Coq_stat_return (Some (exp_to_exp e))
      | Return None -> JsSyntax.Coq_stat_return None
      | Break (Some l) -> JsSyntax.Coq_stat_break (JsSyntax.Coq_label_string (string_to_coq l))
      | Break None -> JsSyntax.Coq_stat_break JsSyntax.Coq_label_empty
      | Continue (Some l) -> JsSyntax.Coq_stat_continue (JsSyntax.Coq_label_string (string_to_coq l))
      | Continue None -> JsSyntax.Coq_stat_continue JsSyntax.Coq_label_empty
      | Debugger -> JsSyntax.Coq_stat_debugger
      | VarDec vs -> JsSyntax.Coq_stat_var_decl (map (fun (v, e) ->
          string_to_coq v, match e with None -> None | Some e -> Some (exp_to_exp e)) vs)
      | Throw e -> JsSyntax.Coq_stat_throw (exp_to_exp e)
      | Label (l, e) -> JsSyntax.Coq_stat_label (string_to_coq l, f e)
	  | While (e1, e2)  -> JsSyntax.Coq_stat_while ([], exp_to_exp e1, f e2)
	  | DoWhile (e1, e2) -> JsSyntax.Coq_stat_do_while ([], f e1, exp_to_exp e2)
      | With (e1, e2) -> JsSyntax.Coq_stat_with (exp_to_exp e1, f e2)
      | Try (e, None, None) -> JsSyntax.Coq_stat_try (f e, None, None)
      | Try (e, None, Some fe) -> JsSyntax.Coq_stat_try (f e, None, Some (f fe))
      | Try (e, Some (s, ce), None) -> JsSyntax.Coq_stat_try (f e, Some (string_to_coq s, f ce), None)
      | Try (e, Some (s, ce), Some fe) -> JsSyntax.Coq_stat_try (f e, Some (string_to_coq s, f ce), Some (f fe))  
      | If (e1, e2, Some e3) -> JsSyntax.Coq_stat_if (exp_to_exp e1, f e2, Some (f e3))
      | If (e1, e2, None) -> JsSyntax.Coq_stat_if (exp_to_exp e1, f e2, None)
      | ForIn (e1, e2, e3) -> raise (CoqSyntaxDoesNotSupport (Pretty_print.string_of_exp false exp))
      | For (e1, e2, e3, e4) ->
        let to_option expr = begin match expr with
                                 | None -> None
                                 | Some(real_e) -> Some (exp_to_exp real_e) end in
        (match e1 with
          | Some ({exp_offset; exp_stx = (VarDec vs); exp_annot}) ->
                JsSyntax.Coq_stat_for_var ([], (map (fun (v, e) ->
                    string_to_coq v, match e with None -> None
                        | Some e -> Some (exp_to_exp e)) vs),
                    to_option e2, to_option e3, f e4)
          | _ ->
                  JsSyntax.Coq_stat_for ([], to_option e1, to_option e2, to_option e3, f e4))
      | Switch (e1, e2s) -> 
        let (firstpart, defaultcase, secondpart) = List.fold_left (fun (fi, de, se) el -> (
          if de = None then
          match el with
            | (DefaultCase, {exp_stx = Block es}) -> (fi, Some (List.map f es), [])
            | (Case cexp, {exp_stx = Block es}) -> (fi @ [JsSyntax.Coq_switchclause_intro (exp_to_exp cexp, List.map f es)], None, [])
            | _ -> raise CannotHappen
          else match el with
            | (Case cexp, {exp_stx = Block es}) -> (fi, de, se @ [JsSyntax.Coq_switchclause_intro (exp_to_exp cexp, List.map f es)])
            | _ -> raise CannotHappen           
          )) ([], None, []) e2s in
        let switchbody = match defaultcase with
          | None -> JsSyntax.Coq_switchbody_nodefault firstpart
          | Some de -> JsSyntax.Coq_switchbody_withdefault (firstpart, de, secondpart) in
        JsSyntax.Coq_stat_switch ([], exp_to_exp e1, switchbody)
      | Block es -> JsSyntax.Coq_stat_block (List.map f es)

      | Script _ -> raise Parser.InvalidArgument

and exp_to_prog exp : JsSyntax.prog =
  match exp.exp_stx with
    | Script (s, e2s) -> JsSyntax.Coq_prog_intro (s, map exp_to_elem e2s)
    | Block (e2s) -> JsSyntax.Coq_prog_intro (false, map exp_to_elem e2s)
    | _ ->  JsSyntax.Coq_prog_intro (false, [exp_to_elem exp])

and exp_to_elem exp : JsSyntax.element = 
    let tos = string_to_coq in
    match exp.exp_stx with
      | FunctionExp (s, (Some name), args, body) -> JsSyntax.Coq_element_func_decl (tos name, map tos args, exp_to_funcbody body s)
      | Function (s, (Some name), args, body) -> JsSyntax.Coq_element_func_decl (tos name, map tos args, exp_to_funcbody body s)
      | _ -> JsSyntax.Coq_element_stat (exp_to_stat exp)

and exp_to_funcbody exp strict : JsSyntax.funcbody =
  let body =
	match exp_to_prog exp with
    | JsSyntax.Coq_prog_intro (_, elems) -> JsSyntax.Coq_prog_intro (strict, elems)
  in JsSyntax.Coq_funcbody_intro (body, [])

let coq_syntax_from_main ?force_strict:(str = false) filename =
  let exp = (Parser_main.exp_from_main ~force_strict:str filename)() in
  exp_to_prog exp

let coq_syntax_from_file ?init:(i = false) ?force_strict:(str = false) filename =
  let exp = Parser_main.exp_from_file ~init:i ~force_strict:(str = false) filename in
  exp_to_prog exp
  
let coq_syntax_from_string s =
  let exp = Parser_main.exp_from_string s in
  exp_to_prog exp

