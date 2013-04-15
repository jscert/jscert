open Interpreter

let prbool = function
	| true -> "true"
	| false -> "false"

let prloc = function
  | Object_loc_normal i -> "@" ^ string_of_int i
  | Object_loc_prealloc builtinid ->
		match builtinid with
		| Prealloc_error -> "Prealloc_error"
		| Prealloc_range_error -> "Prealloc_range_error"
		| Prealloc_ref_error -> "Prealloc_ref_error"
		| Prealloc_syntax_error -> "Prealloc_syntax_error"
		| Prealloc_type_error -> "Prealloc_type_error"
		| Prealloc_global -> "Prealloc_global"
		| Prealloc_global_eval -> "Prealloc_global_eval"
		| Prealloc_global_is_nan -> "Prealloc_global_is_nan"
		| Prealloc_global_is_finite -> "Prealloc_global_is_finite"
		| Prealloc_object -> "Prealloc_object"
		| _ -> "Object_loc_builtin NIY"

let prmutability = function
	| Mutability_uninitialized_immutable -> "Mutability_uninitialized_immutable"
	| Mutability_immutable -> "Mutability_immutable"
	| Mutability_nondeletable -> "Mutability_nondeletable"
	| Mutability_deletable -> "Mutability_deletable"

let prenv_loc i =
	"#" ^ string_of_int i

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

let prvalue = function
  | Value_prim p -> prprim p
  | Value_object ol -> prloc ol

let prattributes = function
  | Attributes_data_of d ->
	Printf.sprintf "{ value: %s, writable: %s, enum: %s, config: %s }"
	  (prvalue (attributes_data_value d))
	  (prbool (attributes_data_writable d))
	  (prbool (attributes_data_enumerable d))
	  (prbool (attributes_data_configurable d))
  | Attributes_accessor_of a ->
	Printf.sprintf "{ get: %s, set: %s, enum: %s, config: %s }"
	  (prvalue (attributes_accessor_get a))
	  (prvalue (attributes_accessor_set a))
	  (prbool (attributes_accessor_enumerable a))
	  (prbool (attributes_accessor_configurable a))


let prfieldmap (old : (prop_name * attributes) list option) skip_init loc obj =
	String.concat "" (List.fold_left
		(fun acc (x, a) ->
			if skip_init
			  && morph_option false (fun old0 ->
				List.mem (x, a) old0) old
			then acc
			else Printf.sprintf "\t %s . %s =  %s;\n"
				  (prloc loc)
				  (string_of_char_list x)
				  (prattributes a)
				    :: acc) []
		(Heap.to_list (obj.object_properties_)))

let prheap =
  let list_heap_init = Heap.to_list object_heap_initial in
  fun skip_init heap ->
  "digraph g{\n" ^
  "node [shape=record];\n" ^
  "rankdir=LR;\n" ^
  (String.concat ""
  	  (List.rev (List.map (fun (key, v) ->
  			prfieldmap (try
  					Some (Heap.to_list
  						(object_properties_
  							(List.assoc key list_heap_init)))
  				with Not_found -> None) skip_init
  			  key v) (Heap.to_list heap)
  	))) ^
  "}"

let prenv_record r =
  String.concat ""
  	  (List.rev (List.map (fun (loc, er) ->
		  prenv_loc loc ^ " -> " ^
		  match er with
		  | Env_record_decl der ->
				String.concat "\n" (List.rev (List.map (fun (x, (mu, v)) ->
					"\t\"" ^ string_of_char_list x ^ "\" -> " ^
					prmutability mu ^ ", " ^ prvalue v
				) (Heap.to_list der)))
		  | Env_record_object (o, this) ->
				prloc o ^ " with provide this = " ^ prbool this
	    ) (Heap.to_list r)
  	))

let prstate skip s =
	"State:\n" ^
	"\tHeap:\n" ^ prheap skip (state_object_heap s) ^
	"\n\tEnv. Record:\n" ^ prenv_record (state_env_record_heap s)

(*
module M1 = Map.Make (struct type t = loc let compare = Pervasives.compare end)
module M2 = Map.Make (struct type t = field let compare = Pervasives.compare end)

let id = ref 0

let new_id () =
	incr id; "__" ^ (string_of_int (!id))
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

