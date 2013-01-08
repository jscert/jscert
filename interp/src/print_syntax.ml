open Batteries_uni
open Interpreter
open List

let string_of_binary_op op =
  match op with
		| Binary_op_add -> "Binary_op_add"
		| Binary_op_mult -> "Binary_op_mult"
		| Binary_op_div -> "Binary_op_div"
		| Binary_op_equal -> "Binary_op_equal"
		| Binary_op_instanceof -> "Binary_op_instanceof"
		| Binary_op_in -> "Binary_op_in"
		| Binary_op_and -> "Binary_op_and"
		| Binary_op_or -> "Binary_op_or"

let string_of_unary_op op =
  match op with
		| Unary_op_not -> "Unary_op_not"
		| Unary_op_delete -> "Unary_op_delete"
		| Unary_op_typeof -> "Unary_op_typeof"
		| Unary_op_pre_incr -> "Unary_op_pre_incr"
		| Unary_op_post_incr -> "Unary_op_post_incr"
		| Unary_op_pre_decr -> "Unary_op_pre_decr"
		| Unary_op_post_decr -> "Unary_op_post_decr"
		| Unary_op_void -> "Unary_op_void"

let string_of_literal l =
  match l with
		| Literal_null -> "Literal_null"
		| Literal_bool b -> Printf.sprintf "Literal_bool %s" (string_of_bool b)
		| Literal_number n -> Printf.sprintf "Literal_number %s" (string_of_float n)
		| Literal_string s -> Printf.sprintf "Literal_string %s" (String.of_list s)

let string_of_args xs =
  String.concat "," (map String.of_list xs)

let rec string_of_expr e =
  let f = string_of_expr in
  match e with
		| Expr_this -> "Expr_this"
		| Expr_variable x -> Printf.sprintf "Expr_variable (%s)" (String.of_list x)
		| Expr_literal l -> Printf.sprintf "Expr_literal (%s)" (string_of_literal l)
		| Expr_object l -> Printf.sprintf "Expr_object (%s)" 
      (String.concat "; " (map (fun (x, e) -> Printf.sprintf "%s : %s" (String.of_list x) (f e)) l))
		| Expr_function (n, xs, p) -> 
      let name = match n with 
        | None -> "None"
        | Some n -> Printf.sprintf "Some %s" (String.of_list n) in
      Printf.sprintf "Expr_function (%s, %s, %s)" name (string_of_args xs) (string_of_prog p)
	  | Expr_access (e1, e2) -> Printf.sprintf "Expr_access (%s, %s)" (f e1) (f e2)
		| Expr_member (e, x) -> Printf.sprintf "Expr_member (%s, %s)" (f e) (String.of_list x)
		| Expr_new (e1, e2s) -> Printf.sprintf "Expr_new (%s, %s)" (f e1) (String.concat "," (map f e2s))
		| Expr_call (e1, e2s) -> Printf.sprintf "Expr_call (%s, %s)" (f e1) (String.concat "," (map f e2s))
		| Expr_unary_op (op, e) -> Printf.sprintf "Expr_unary_op (%s, %s)" (string_of_unary_op op) (f e)
		| Expr_binary_op (e1, op, e2) -> 
      Printf.sprintf "Expr_binary_op (%s, %s, %s)" (f e1) (string_of_binary_op op) (f e2)
		| Expr_assign (e1, op, e2) ->
      let op = match op with
        | None -> "None"
        | Some op -> Printf.sprintf "Some %s" (string_of_binary_op op) in
      Printf.sprintf "Expr_assign (%s, %s, %s)" (f e1) op (f e2)
and string_of_stat s =
  let f = string_of_stat in
  match s with
		| Stat_expr e -> Printf.sprintf "Stat_expr (%s)" (string_of_expr e)
		| Stat_seq (s1, s2) -> Printf.sprintf "Stat_seq (%s, %s)\n" (f s1) (f s2)
		| Stat_var_decl (x, e) -> 
      let e = match e with 
        | None -> "None"
        | Some e -> Printf.sprintf "Some (%s)" (string_of_expr e) in
      Printf.sprintf "Stat_var_decl (%s, %s)" (String.of_list x) e
		| Stat_if (e, s1, s2) -> 
      let s2 = match s2 with
        | None -> "None"
        | Some s2 -> Printf.sprintf "Some (%s)" (f s2) in
      Printf.sprintf "Stat_if (%s, %s, %s)" (string_of_expr e) (f s1) s2
		| Stat_while (e, s) -> Printf.sprintf "Stat_while (%s, %s)" (string_of_expr e) (f s)
		| Stat_with (e, s) -> Printf.sprintf "Stat_with (%s, %s)" (string_of_expr e) (f s)
		| Stat_throw e -> Printf.sprintf "Stat_throw (%s)" (string_of_expr e)
		| Stat_try (s, xso, so) ->
      let xso = match xso with
        | None -> "None"
        | Some (x, s) -> Printf.sprintf "Some (%s, %s)" (String.of_list x) (f s) in
      let so = match so with
        | None -> "None"
        | Some s -> Printf.sprintf "Some (%s)" (f s) in
      Printf.sprintf "Stat_try (%s, %s, %s)" (f s) xso so
		| Stat_skip -> "Stat_skip"
and string_of_prog p =
  let f = string_of_prog in
  match p with
		| Prog_stat s -> Printf.sprintf "Prog_stat (%s)\n" (string_of_stat s)
		| Prog_seq (p1, p2) -> Printf.sprintf "Prog_seq (%s, %s)" (f p1) (f p2)
		| Prog_function_decl (n, xs, p) -> 
      Printf.sprintf "Prog_function_decl (%s, %s, %s)" (String.of_list n) (string_of_args xs) (f p)