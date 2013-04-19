open Shared
open JsSyntax
open JsInit

let prbool = function
	| true -> "true"
	| false -> "false"

let proption f = function
	| None -> "None"
	| Some x -> "Some (" ^ f x ^ ")"

let prprealloc = function
  | Coq_prealloc_global -> "Coq_prealloc_global"
  | Coq_prealloc_global_eval -> "Coq_prealloc_global_eval"
  | Coq_prealloc_global_is_finite -> "Coq_prealloc_global_is_finite"
  | Coq_prealloc_global_is_nan -> "Coq_prealloc_global_is_nan"
  | Coq_prealloc_global_parse_float -> "Coq_prealloc_global_parse_float"
  | Coq_prealloc_global_parse_int -> "Coq_prealloc_global_parse_int"
  | Coq_prealloc_object -> "Coq_prealloc_object"
  | Coq_prealloc_object_get_proto_of -> "Coq_prealloc_object_get_proto_of"
  | Coq_prealloc_object_get_own_prop_descriptor -> "Coq_prealloc_object_get_own_prop_descriptor"
  | Coq_prealloc_object_get_own_prop_name -> "Coq_prealloc_object_get_own_prop_name"
  | Coq_prealloc_object_create -> "Coq_prealloc_object_create"
  | Coq_prealloc_object_define_prop -> "Coq_prealloc_object_define_prop"
  | Coq_prealloc_object_define_properties -> "Coq_prealloc_object_define_properties"
  | Coq_prealloc_object_seal -> "Coq_prealloc_object_seal"
  | Coq_prealloc_object_freeze -> "Coq_prealloc_object_freeze"
  | Coq_prealloc_object_prevent_extensions -> "Coq_prealloc_object_prevent_extensions"
  | Coq_prealloc_object_is_sealed -> "Coq_prealloc_object_is_sealed"
  | Coq_prealloc_object_is_frozen -> "Coq_prealloc_object_is_frozen"
  | Coq_prealloc_object_is_extensible -> "Coq_prealloc_object_is_extensible"
  | Coq_prealloc_object_keys -> "Coq_prealloc_object_keys"
  | Coq_prealloc_object_keys_call -> "Coq_prealloc_object_keys_call"
  | Coq_prealloc_object_proto -> "Coq_prealloc_object_proto"
  | Coq_prealloc_object_proto_to_string -> "Coq_prealloc_object_proto_to_string"
  | Coq_prealloc_object_proto_value_of -> "Coq_prealloc_object_proto_value_of"
  | Coq_prealloc_object_proto_has_own_prop -> "Coq_prealloc_object_proto_has_own_prop"
  | Coq_prealloc_object_proto_is_prototype_of -> "Coq_prealloc_object_proto_is_prototype_of"
  | Coq_prealloc_object_proto_prop_is_enumerable -> "Coq_prealloc_object_proto_prop_is_enumerable"
  | Coq_prealloc_function -> "Coq_prealloc_function"
  | Coq_prealloc_function_proto -> "Coq_prealloc_function_proto"
  | Coq_prealloc_function_proto_to_string -> "Coq_prealloc_function_proto_to_string"
  | Coq_prealloc_function_proto_apply -> "Coq_prealloc_function_proto_apply"
  | Coq_prealloc_function_proto_bind -> "Coq_prealloc_function_proto_bind"
  | Coq_prealloc_bool -> "Coq_prealloc_bool"
  | Coq_prealloc_bool_proto -> "Coq_prealloc_bool_proto"
  | Coq_prealloc_bool_proto_to_string -> "Coq_prealloc_bool_proto_to_string"
  | Coq_prealloc_bool_proto_value_of -> "Coq_prealloc_bool_proto_value_of"
  | Coq_prealloc_number -> "Coq_prealloc_number"
  | Coq_prealloc_number_proto -> "Coq_prealloc_number_proto"
  | Coq_prealloc_number_proto_to_string -> "Coq_prealloc_number_proto_to_string"
  | Coq_prealloc_number_proto_value_of -> "Coq_prealloc_number_proto_value_of"
  | Coq_prealloc_number_proto_to_fixed -> "Coq_prealloc_number_proto_to_fixed"
  | Coq_prealloc_number_proto_to_exponential -> "Coq_prealloc_number_proto_to_exponential"
  | Coq_prealloc_number_proto_to_precision -> "Coq_prealloc_number_proto_to_precision"
  | Coq_prealloc_array -> "Coq_prealloc_array"
  | Coq_prealloc_array_is_array -> "Coq_prealloc_array_is_array"
  | Coq_prealloc_array_proto -> "Coq_prealloc_array_proto"
  | Coq_prealloc_array_proto_to_string -> "Coq_prealloc_array_proto_to_string"
  | Coq_prealloc_string -> "Coq_prealloc_string"
  | Coq_prealloc_string_proto -> "Coq_prealloc_string_proto"
  | Coq_prealloc_string_proto_to_string -> "Coq_prealloc_string_proto_to_string"
  | Coq_prealloc_string_proto_value_of -> "Coq_prealloc_string_proto_value_of"
  | Coq_prealloc_string_proto_char_at -> "Coq_prealloc_string_proto_char_at"
  | Coq_prealloc_string_proto_char_code_at -> "Coq_prealloc_string_proto_char_code_at"
  | Coq_prealloc_math -> "Coq_prealloc_math"
  | Coq_prealloc_mathop -> "Coq_prealloc_mathop"
  | Coq_prealloc_error -> "Coq_prealloc_error"
  | Coq_prealloc_range_error -> "Coq_prealloc_range_error"
  | Coq_prealloc_ref_error -> "Coq_prealloc_ref_error"
  | Coq_prealloc_syntax_error -> "Coq_prealloc_syntax_error"
  | Coq_prealloc_type_error -> "Coq_prealloc_type_error"
  | Coq_prealloc_throw_type_error -> "Coq_prealloc_throw_type_error"


let prloc = function
  | Coq_object_loc_normal i -> "@" ^ string_of_int i
  | Coq_object_loc_prealloc builtinid ->
		prprealloc builtinid

let prmutability = function
	| Coq_mutability_uninitialized_immutable -> "Coq_mutability_uninitialized_immutable"
	| Coq_mutability_immutable -> "Coq_mutability_immutable"
	| Coq_mutability_nondeletable -> "Coq_mutability_nondeletable"
	| Coq_mutability_deletable -> "Coq_mutability_deletable"

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
	| Coq_binary_op_add -> "+"
	| Coq_binary_op_mult -> "*"
	| Coq_binary_op_div -> "/"
	| Coq_binary_op_equal -> "==="
	| Coq_binary_op_instanceof -> "instanceof"
	| Coq_binary_op_in -> "in"
	| _ -> "Binary Op NIY"

let prliteral = function
	| Coq_literal_null -> "null"
	| Coq_literal_bool b -> string_of_bool b
	| Coq_literal_number f -> string_of_float f
	| Coq_literal_string cl -> string_of_char_list cl

let prprim = function
  | Coq_prim_undef -> "undefined"
  | Coq_prim_null -> "null"
  | Coq_prim_bool b -> string_of_bool b
  | Coq_prim_number f -> string_of_float f
  | Coq_prim_string cl -> string_of_char_list cl

let prvalue = function
  | Coq_value_prim p -> prprim p
  | Coq_value_object ol -> prloc ol

let prattributes = function
  | Coq_attributes_data_of d ->
	Printf.sprintf "{ value: %s, writable: %s, enum: %s, config: %s }"
	  (prvalue (attributes_data_value d))
	  (prbool (attributes_data_writable d))
	  (prbool (attributes_data_enumerable d))
	  (prbool (attributes_data_configurable d))
  | Coq_attributes_accessor_of a ->
	Printf.sprintf "{ get: %s, set: %s, enum: %s, config: %s }"
	  (prvalue (attributes_accessor_get a))
	  (prvalue (attributes_accessor_set a))
	  (prbool (attributes_accessor_enumerable a))
	  (prbool (attributes_accessor_configurable a))

let prfull_descriptor = function
	| Coq_full_descriptor_undef -> "undef"
	| Coq_full_descriptor_some a -> "attribute: " ^ prattributes a

let prdescriptor desc =
	Printf.sprintf "{ value : %s ; writable : %s ; get : %s  ; set : %s ; enumerable : %s ; configurable : %s }"
	  (proption prvalue desc.descriptor_value)
	  (proption prbool desc.descriptor_writable)
	  (proption prvalue desc.descriptor_get)
	  (proption prvalue desc.descriptor_set)
	  (proption prbool desc.descriptor_enumerable)
	  (proption prbool desc.descriptor_configurable)


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
		  | Coq_env_record_decl der ->
				String.concat "\n" (List.rev (List.map (fun (x, (mu, v)) ->
					"\t\"" ^ string_of_char_list x ^ "\" -> " ^
					prmutability mu ^ ", " ^ prvalue v
				) (Heap.to_list der)))
		  | Coq_env_record_object (o, this) ->
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
  | Coq_expr_this -> "Expr_this"
  | Coq_expr_identifier _ -> "Expr_identifier"
  | Coq_expr_literal _ -> "Expr_literal"
  | Coq_expr_object _ -> "Expr_object"
  | Coq_expr_function _ -> "Expr_function"
  | Coq_expr_access _ -> "Expr_access"
  | Coq_expr_member _ -> "Expr_member"
  | Coq_expr_new _ -> "Expr_new"
  | Coq_expr_call _ -> "Expr_call"
  | Coq_expr_unary_op _ -> "Expr_unary_op"
  | Coq_expr_binary_op _ -> "Expr_binary_op"
  | Coq_expr_conditional _ -> "Expr_conditional"
  | Coq_expr_assign _ -> "Expr_assign"

let dump_propbody_step = function
  | Coq_propbody_val _ -> "Propbody_val"
  | Coq_propbody_get _ -> "Propbody_get"
  | Coq_propbody_set _ -> "Propbody_set"

let dump_funcbody_step = function
  | Coq_funcbody_intro _ -> "Funcbody_intro"

let dump_stat_step = function
  | Coq_stat_expr _ -> "Stat_expr"
  | Coq_stat_block _ -> "Stat_block"
  | Coq_stat_label _ -> "Stat_label"
  | Coq_stat_var_decl _ -> "Stat_var_decl"
  | Coq_stat_if _ -> "Stat_if"
  | Coq_stat_while _ -> "Stat_while"
  | Coq_stat_do_while _ -> "Stat_do_while"
  | Coq_stat_with _ -> "Stat_with"
  | Coq_stat_throw _ -> "Stat_throw"
  | Coq_stat_return _ -> "Stat_return"
  | Coq_stat_break _ -> "Stat_break"
  | Coq_stat_continue _ -> "Stat_continue"
  | Coq_stat_try _ -> "Stat_try"
  | Coq_stat_for_in _ -> "Stat_for_in"
  | Coq_stat_for_in_var _ -> "Stat_for_in_var"
  | Coq_stat_debugger -> "Stat_debugger"

let dump_prog_step = function
  | Coq_prog_intro (b, es) ->
		String.concat " ; "
		  (List.map (function
			| Coq_element_stat _ -> "Element_stat"
			| Coq_element_func_decl _ -> "Element_func_decl") es)

