open Interpreter

let prloc = function
  | Object_loc_normal i -> "@" ^ string_of_int i
  | Object_loc_builtin builtinid ->
		match builtinid with
		| Builtin_error -> "Builtin_error"
		| Builtin_range_error -> "Builtin_range_error"
		| Builtin_ref_error -> "Builtin_ref_error"
		| Builtin_syntax_error -> "Builtin_syntax_error"
		| Builtin_type_error -> "Builtin_type_error"
		| Builtin_global -> "Builtin_global"
		| Builtin_global_eval -> "Builtin_global_eval"
		| Builtin_global_eval_call -> "Builtin_global_eval_call"
		| Builtin_global_is_nan -> "Builtin_global_is_nan"
		| Builtin_global_is_nan_call -> "Builtin_global_is_nan_call"
		| Builtin_global_is_finite -> "Builtin_global_is_finite"
		| Builtin_global_is_finite_call -> "Builtin_global_is_finite_call"
		| Builtin_object -> "Builtin_object"
		| _ -> "Object_loc_builtin NIY"

let string_of_char_list cl =
	let s = String.create (List.length cl) in
	let rec set_str n = function
		| [] -> ()
		| c :: tl -> s.[n] <- c; set_str (n+1) tl
	in set_str 0 cl; s

let char_list_of_string s =
	let rec acc_ch acc n =
		if n < 0 then acc else acc_ch ((String.get s n)::acc) (n-1)
	in
	acc_ch [] ((String.length s) - 1)

let prbinary_op = function
	| Binary_op_add -> "+"
	| Binary_op_mult -> "*"
	| Binary_op_div -> "/"
	| Binary_op_equal -> "==="
	| Binary_op_instanceof -> "instanceof"
	| Binary_op_in -> "in"
  | _ -> "Binary Op NIY"

let prliteral = function
	| Literal_null -> "null"
	| Literal_bool b -> string_of_bool b
	| Literal_number f -> string_of_float f
	| Literal_string cl -> string_of_char_list cl

let prprim = function
  | Prim_undef -> "undefined"
  | Prim_null -> "null"
  | Prim_bool b -> string_of_bool b
  | Prim_number f -> string_of_float f
  | Prim_string cl -> string_of_char_list cl

let rec prvalue = function
  | Value_prim p -> prprim p
  | Value_object ol -> prloc ol


let prfieldmap loc obj =
	String.concat "" (List.fold_left
		(fun acc (x, a) ->
			("\t" ^ prloc loc ^ "." ^ string_of_char_list x ^ ";\n") :: acc) []
		(Interpreter.Heap.to_list (obj.Interpreter.object_properties_)))

let prheap heap =
	"digraph g{\n" ^
	"node [shape=record];\n" ^
	"rankdir=LR;\n" ^
	(String.concat ""
		  (List.rev (List.fold_left
			(fun acc (key, v) -> prfieldmap key v :: acc) []
			(Interpreter.Heap.to_list heap)
		))) ^
	"}"

(*

let rec prexpr = function
  | Expr_this -> "this"
	| Expr_variable cl -> Printf.sprintf "%s" (string_of_char_list cl)
	| Expr_literal v -> Printf.sprintf "%s" (prliteral v)
	| Expr_object ol -> "Expr_object {" ^ String.concat ", " (List.map (fun (x,e) -> string_of_char_list x ^ ": " ^ prexpr e) ol) ^ "}"
	| Expr_function (clo, cll, e) -> Printf.sprintf "function %s(%s){ %s }"
		(match clo with None -> "" | Some cl -> string_of_char_list cl)
		(String.concat ", " (List.map string_of_char_list cll))
		(prprog e)
  | Expr_access _ -> "NIY"
	| Expr_member (e1, cl) -> Printf.sprintf "(%s).%s"
		(prexpr e1) (string_of_char_list cl)
	| Expr_new (e, el) -> Printf.sprintf "new (%s) (%s)"
		(prexpr e) (String.concat ", " (List.map prexpr el))
	| Expr_call (e, el) -> Printf.sprintf "(%s) (%s)"
		(prexpr e) (String.concat ", " (List.map prexpr el))
	| Expr_assign (e1, bo, e2) -> Printf.sprintf "%s %s= %s"
																							 (prexpr e1)
																							 (match bo with
																								| None -> ""
																								| Some b -> prbinary_op b)
																							 (prexpr e2)
	| _ -> "PR NIY\n"

and prstat = function
  | Stat_expr e -> prexpr e
  | Stat_seq (s1,s2) -> (prstat s1) ^ ";\n" ^ (prstat s2)
  | Stat_var_decl (v, eo) -> "var " ^ (string_of_char_list v)
                             ^ (match eo with None -> "" 
                                            | Some e -> prexpr e)
  | Stat_if (e, s, so) -> "if (" ^ (prexpr e) ^") {\n" ^ prstat s ^
                            (match so with None -> "}"
                                         | Some s -> "} {\n" ^ (prstat s) ^ "}")
  | _ -> "NIY"

and prprog = function
  | Prog_stat s -> prstat s
  | Prog_seq (s1,s2) -> (prprog s1) ^ ";\n" ^ (prprog s2)
  | Prog_function_decl (s, sl, p) ->
     Printf.sprintf
       "function %s(%s) {%s}"
       (string_of_char_list s)
       (String.concat ", " (List.map string_of_char_list sl))
       (prprog p)
                                       

module M1 = Map.Make (struct type t = loc let compare = Pervasives.compare end)
module M2 = Map.Make (struct type t = field let compare = Pervasives.compare end)

let id = ref 0

let new_id () =
	incr id; "__" ^ (string_of_int (!id))

let prfields locs prproto prthis field value =
	match field, value with
		| Field_proto, Value_loc l ->
			if prproto then
			Printf.sprintf "%s -> %s [label=\"%s\"];\n" locs (prloc l) (prfield field)
			else ""
		| Field_this, Value_loc l ->
			if prthis then
			Printf.sprintf "%s -> %s [label=\"%s\"];\n" locs (prloc l) (prfield field)
			else ""
		| field, Value_loc l ->
			Printf.sprintf "%s -> %s [label=\"%s\"];\n" locs (prloc l) (prfield field)
		| field, value ->
			let i = new_id () in
			Printf.sprintf
				"%s [label=\"%s\", shape=note];\n%s -> %s [label=\"%s\"];\n"
				i (prvalue value) locs i (prfield field)

let prfieldmap loc fm =
	let proto,prproto =
		try
			let pr = M2.find Field_proto fm in
			match pr with
				| Value_loc Loc_null -> "null", false
				| Value_loc Loc_obj_proto -> "obj_pr", false
				| Value_loc Loc_func_proto -> "func_pr", false
				| _ -> "", true
		with
			| Not_found -> "", true
	in
	let this,prthis =
		try
			let th = M2.find Field_this fm in
			match th with
				| Value_loc Loc_global -> "glob", false
				| _ -> "", true
		with
			| Not_found -> "", true
	in
	let prl = prloc loc in
	(Printf.sprintf "%s [label=\"%s|{%s|%s}\"];\n" prl prl proto this) ^
		(String.concat ""
									 (M2.fold
											(fun key v acc ->
											 (prfields prl prproto prthis key v) :: acc)
											fm []))
		
let prheap heapmap =
	"digraph g{\n" ^
	"node [shape=record];\n" ^
	"rankdir=LR;\n" ^
		(String.concat ""
									 (List.rev (M1.fold
											(fun key v acc -> (prfieldmap key v) :: acc)
											heapmap
											[]
		))) ^
	"}"

let cell_to_map map (Ref (loc, field), value) =
  let locm = try M1.find loc map with Not_found -> M2.empty in
	M1.add loc
		(if (M2.mem field locm) then locm else
				M2.add field value locm) map
	
let create_heap_map = List.fold_left cell_to_map M1.empty

let main h = prheap (create_heap_map (Heap.to_list h))

let print_to_file f h=
	let oc = open_out f in
	output_string oc (main h);
	close_out oc
 *)


let dump_expr_step = function
  | Expr_this -> "Expr_this"
  | Expr_identifier _ -> "Expr_identifier"
  | Expr_literal _ -> "Expr_literal"
  | Expr_object _ -> "Expr_object"
  | Expr_function _ -> "Expr_function"
  | Expr_access _ -> "Expr_access"
  | Expr_member _ -> "Expr_member"
  | Expr_new _ -> "Expr_new"
  | Expr_call _ -> "Expr_call"
  | Expr_unary_op _ -> "Expr_unary_op"
  | Expr_binary_op _ -> "Expr_binary_op"
  | Expr_conditional _ -> "Expr_conditional"
  | Expr_assign _ -> "Expr_assign"

let dump_propbody_step = function
  | Propbody_val _ -> "Propbody_val"
  | Propbody_get _ -> "Propbody_get"
  | Propbody_set _ -> "Propbody_set"

let dump_funcbody_step = function
  | Funcbody_intro _ -> "Funcbody_intro"

let dump_stat_step = function
  | Stat_expr _ -> "Stat_expr"
  | Stat_block _ -> "Stat_block"
  | Stat_label _ -> "Stat_label"
  | Stat_var_decl _ -> "Stat_var_decl"
  | Stat_if _ -> "Stat_if"
  | Stat_while _ -> "Stat_while"
  | Stat_do_while _ -> "Stat_do_while"
  | Stat_with _ -> "Stat_with"
  | Stat_throw _ -> "Stat_throw"
  | Stat_return _ -> "Stat_return"
  | Stat_break _ -> "Stat_break"
  | Stat_continue _ -> "Stat_continue"
  | Stat_try _ -> "Stat_try"
  | Stat_for_in _ -> "Stat_for_in"
  | Stat_for_in_var _ -> "Stat_for_in_var"
  | Stat_debugger -> "Stat_debugger"

let dump_prog_step = function
  | Prog_intro (b, es) ->
		String.concat " ; "
		  (List.map (function
			| Element_stat _ -> "Element_stat"
			| Element_func_decl _ -> "Element_func_decl") es)

