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
  | Coq_prealloc_global_parse_int -> "Coq_prealloc_global_parse_int"
  | Coq_prealloc_global_parse_float -> "Coq_prealloc_global_parse_float"
  | Coq_prealloc_global_is_finite -> "Coq_prealloc_global_is_finite"
  | Coq_prealloc_global_is_nan -> "Coq_prealloc_global_is_nan"
  | Coq_prealloc_global_decode_uri -> "Coq_prealloc_global_decode_uri"
  | Coq_prealloc_global_decode_uri_component -> "Coq_prealloc_global_decode_uri_component"
  | Coq_prealloc_global_encode_uri -> "Coq_prealloc_global_encode_uri"
  | Coq_prealloc_global_encode_uri_component -> "Coq_prealloc_global_encode_uri_component"
  | Coq_prealloc_object -> "Coq_prealloc_object"
  | Coq_prealloc_object_get_proto_of -> "Coq_prealloc_object_get_proto_of"
  | Coq_prealloc_object_get_own_prop_descriptor -> "Coq_prealloc_object_get_own_prop_descriptor"
  | Coq_prealloc_object_get_own_prop_name -> "Coq_prealloc_object_get_own_prop_name"
  | Coq_prealloc_object_create -> "Coq_prealloc_object_create"
  | Coq_prealloc_object_define_prop -> "Coq_prealloc_object_define_prop"
  | Coq_prealloc_object_define_props -> "Coq_prealloc_object_define_props"
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
  | Coq_prealloc_function_proto_call -> "Coq_prealloc_function_proto_call"
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
  | Coq_prealloc_array_proto_join -> "Coq_prealloc_array_proto_join"
  | Coq_prealloc_array_proto_pop -> "Coq_prealloc_array_proto_pop"
  | Coq_prealloc_array_proto_push -> "Coq_prealloc_array_proto_push"
  | Coq_prealloc_array_proto_to_string -> "Coq_prealloc_array_proto_to_string"
  | Coq_prealloc_string -> "Coq_prealloc_string"
  | Coq_prealloc_string_proto -> "Coq_prealloc_string_proto"
  | Coq_prealloc_string_proto_to_string -> "Coq_prealloc_string_proto_to_string"
  | Coq_prealloc_string_proto_value_of -> "Coq_prealloc_string_proto_value_of"
  | Coq_prealloc_string_proto_char_at -> "Coq_prealloc_string_proto_char_at"
  | Coq_prealloc_string_proto_char_code_at -> "Coq_prealloc_string_proto_char_code_at"
  | Coq_prealloc_math -> "Coq_prealloc_math"
  | Coq_prealloc_mathop _ -> "Coq_prealloc_mathop"
  | Coq_prealloc_date -> "Coq_prealloc_date"
  | Coq_prealloc_regexp -> "Coq_prealloc_regexp"
  | Coq_prealloc_error -> "Coq_prealloc_error"
  | Coq_prealloc_native_error Coq_native_error_eval -> "Coq_prealloc_native_error_eval"
  | Coq_prealloc_native_error Coq_native_error_range -> "Coq_prealloc_native_error_range"
  | Coq_prealloc_native_error Coq_native_error_ref -> "Coq_prealloc_native_error_ref"
  | Coq_prealloc_native_error Coq_native_error_syntax -> "Coq_prealloc_native_error_syntax"
  | Coq_prealloc_native_error Coq_native_error_type -> "Coq_prealloc_native_error_type"
  | Coq_prealloc_native_error Coq_native_error_uri -> "Coq_prealloc_native_error_uri"
  | Coq_prealloc_native_error_proto Coq_native_error_eval -> "Coq_prealloc_native_error_proto_eval"
  | Coq_prealloc_native_error_proto Coq_native_error_range -> "Coq_prealloc_native_error_proto_range"
  | Coq_prealloc_native_error_proto Coq_native_error_ref -> "Coq_prealloc_native_error_proto_ref"
  | Coq_prealloc_native_error_proto Coq_native_error_syntax -> "Coq_prealloc_native_error_proto_syntax"
  | Coq_prealloc_native_error_proto Coq_native_error_type -> "Coq_prealloc_native_error_proto_type"
  | Coq_prealloc_native_error_proto Coq_native_error_uri -> "Coq_prealloc_native_error_proto_uri"
  | Coq_prealloc_throw_type_error -> "Coq_prealloc_throw_type_error"
  | Coq_prealloc_error_proto -> "Coq_prealloc_error_proto"
  | Coq_prealloc_error_proto_to_string -> "Coq_prealloc_error_proto_to_string"
  | Coq_prealloc_json -> "Coq_prealloc_json"


let prcall = function
  | Coq_call_default -> "Coq_call_default"
  | Coq_call_after_bind -> "Coq_call_after_bind"
  | Coq_call_prealloc pa -> "Coq_call_prealloc " ^ prprealloc pa

let prconstruct = function
  | Coq_construct_default -> "Coq_construct_default"
  | Coq_construct_after_bind -> "Coq_construct_after_bind"
  | Coq_construct_prealloc pa -> "Coq_construct_prealloc " ^ prprealloc pa

let prhas_instance = function
  | Coq_builtin_has_instance_function -> "Coq_builtin_has_instance_function"
  | Coq_builtin_has_instance_after_bind -> "Coq_builtin_has_instance_after_bind"

let prget = function
  | Coq_builtin_get_default -> "Coq_builtin_get_default"
  | Coq_builtin_get_function -> "Coq_builtin_get_function"
  | Coq_builtin_get_args_obj -> "Coq_builtin_get_args_obj"

let prdelete = function
  | Coq_builtin_delete_default -> "Coq_builtin_delete_default"
  | Coq_builtin_delete_args_obj -> "Coq_builtin_delete_args_obj"

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

let prlexical_env l =
    String.concat ", " (List.map prenv_loc l)

let string_of_char_list cl =
	let s = String.create (List.length cl) in
	let rec set_str n = function
		| [] -> ()
		| c :: tl -> s.[n] <- c; set_str (n+1) tl
	in set_str 0 cl; s

let prprop_name = string_of_char_list

let prlabel = function
    | Coq_label_empty -> "<empty>"
    | Coq_label_string l -> "label:" ^ string_of_char_list l

let prlabel_set s =
    "{ " ^ String.concat "; " (List.map prlabel s) ^ " }"

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
  | Coq_prim_string cl -> "\"" ^ string_of_char_list cl ^ "\""

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

let remove_siblings l =
    let l' = List.stable_sort (fun (k1, _) (k2, _) -> compare k1 k2) l in
    let rec aux = function
    | [] -> []
    | (k1, v) :: (k2, _) :: l when k1 = k2 ->
        aux ((k1, v) :: l)
    | a :: l -> a :: aux l
    in aux l'

let heap_to_list h =
    remove_siblings (Heap.to_list h)

let probject_properties_aux skip_init old str p =
	String.concat "" (List.fold_left
		(fun acc (x, a) ->
			if skip_init
			  && option_case false (fun old0 ->
				List.mem (x, a) old0) old
			then acc
			else Printf.sprintf "\t %s %s = %s;\n"
                  str
				  (string_of_char_list x)
				  (prattributes a)
				    :: acc) []
		(heap_to_list p))

let probject_properties = probject_properties_aux false None ""

let prfieldmap (old : (prop_name * attributes) list option) skip_init loc obj =
    probject_properties_aux skip_init old (prloc loc ^ " .") (obj.object_properties_)


let prheap =
  let list_heap_init = heap_to_list object_heap_initial in
  fun skip_init heap ->
  "digraph g{\n" ^
  "node [shape=record];\n" ^
  "rankdir=LR;\n" ^
  (String.concat ""
  	  (List.rev (List.map (fun (key, v) ->
        let str =
          let old =
              try Some (List.assoc key list_heap_init)
              with Not_found -> None in
  	      prfieldmap (option_case None (fun obj ->
  	      		Some (heap_to_list (object_properties_ obj))) old)
  	      	skip_init key v ^
          String.concat "" (
              let pr s p g =
                if p (g v) = "" || (skip_init
                  && option_case false (fun obj ->
                    g v = g obj) old)
                then ""
                else
                    Printf.sprintf "\t %s @ %s = %s;\n"
                      (prloc key) s (p (g v)) in [
                  pr "proto" prvalue object_proto_ ;
                  pr "class" string_of_char_list object_class_ ;
                  pr "this" (option_case "" prvalue) (fun obj -> obj.object_bound_this_) ;
                  pr "call" (option_case "" prcall) object_call_ ;
                  pr "construct" (option_case "" prconstruct) object_construct_ ;
                  pr "has_instance" (option_case "" prhas_instance) object_has_instance_ ;
                  pr "prim_value" (option_case "" prvalue) object_prim_value_ ;
                  pr "extensible" prbool object_extensible_ ;
                  pr "get" prget object_get_ ;
                  pr "delete" prdelete (fun obj -> obj.object_delete_) ;
                  pr "scope" (option_case "" prlexical_env) object_scope_ ;
              ]) in
        if str = "" then Printf.sprintf "\t %s, an object;\n" (prloc key)
        else str) (heap_to_list heap)
  	))) ^
  "}"

let prenv_record r =
  String.concat "\n"
  	  (List.rev (List.map (fun (loc, er) ->
		  prenv_loc loc ^ " -> " ^
		  match er with
		  | Coq_env_record_decl der ->
				String.concat "\n" (List.rev (List.map (fun (x, (mu, v)) ->
					"\t\"" ^ string_of_char_list x ^ "\" -> " ^
					prmutability mu ^ ", " ^ prvalue v
				) (heap_to_list der)))
		  | Coq_env_record_object (o, this) ->
				prloc o ^ " with provide this = " ^ prbool this
	    ) (heap_to_list r)
  	))

let prstate skip s =
	"State:\n" ^
	"\tHeap:\n" ^ prheap skip (state_object_heap s) ^
	"\n\tEnv. Record:\n" ^ prenv_record (state_env_record_heap s)

let formatterstate formatter state =
  Format.fprintf formatter "%s" (prstate false state)
  

let prrestype = function
  | Coq_restype_normal -> "normal"
  | Coq_restype_break -> "break"
  | Coq_restype_continue -> "continue"
  | Coq_restype_return -> "return"
  | Coq_restype_throw -> "throw"

let prref_base_type = function
  | Coq_ref_base_type_value v -> "value: " ^ prvalue v
  | Coq_ref_base_type_env_loc l -> "env_loc: " ^ prenv_loc l

let prref { ref_base = rb ; ref_name = rn ; ref_strict = str } =
    (if str then "strict " else "") ^ "ref: (" ^ prref_base_type rb ^ ") . " ^ prprop_name rn

let prresvalue = function
  | Coq_resvalue_empty -> "Coq_resvalue_empty"
  | Coq_resvalue_value v -> "Coq_resvalue_value: " ^ prvalue v
  | Coq_resvalue_ref r -> "Coq_resvalue_ref: " ^ prref r

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
  | Coq_expr_array _ -> "Expr_array"
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
  | Coq_stat_label (l, _) -> "Stat_label: " ^ string_of_char_list l
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
  | Coq_stat_for _ -> "Stat_for"
  | Coq_stat_for_var _ -> "Stat_for_var"
  | Coq_stat_for_in _ -> "Stat_for_in"
  | Coq_stat_for_in_var _ -> "Stat_for_in_var"
  | Coq_stat_debugger -> "Stat_debugger"
  | Coq_stat_switch (_, _, _) -> "Stat_switch"

let dump_prog_step = function
  | Coq_prog_intro (b, es) ->
		String.concat " ; "
		  (List.map (function
			| Coq_element_stat _ -> "Element_stat"
			| Coq_element_func_decl _ -> "Element_func_decl") es)

