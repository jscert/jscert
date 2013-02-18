Set Implicit Arguments.
Require Export Shared.
Require Export Ascii String.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc
  LibHeap LibStream.
Module Heap := LibHeap.HeapList.
Require JsNumber.
Notation "'number'" := (JsNumber.number).



(************************************************************)
(************************************************************)
(************************************************************)
(************************************************************)
(** * Javascript: Syntax *)

(**************************************************************)
(** ** Representation of syntax (11, 12, 13 and 14) *)

(* Unary operator *)

Inductive unary_op :=
  | unary_op_delete
  | unary_op_void
  | unary_op_typeof
  | unary_op_post_incr
  | unary_op_post_decr
  | unary_op_pre_incr
  | unary_op_pre_decr
  | unary_op_add
  | unary_op_neg
  | unary_op_bitwise_not  
  | unary_op_not.

(** Binary operators *)

Inductive binary_op :=
  | binary_op_mult
  | binary_op_div
  | binary_op_mod
  | binary_op_add
  | binary_op_sub
  | binary_op_left_shift
  | binary_op_right_shift
  | binary_op_unsigned_right_shift
  | binary_op_lt
  | binary_op_gt
  | binary_op_le
  | binary_op_ge
  | binary_op_instanceof
  | binary_op_in
  | binary_op_equal
  | binary_op_disequal
  | binary_op_strict_equal
  | binary_op_strict_disequal
  | binary_op_bitwise_and
  | binary_op_bitwise_or
  | binary_op_bitwise_xor
  | binary_op_and
  | binary_op_or
  | binary_op_coma.

(** Grammar of literals *)

Inductive literal :=
  | literal_null : literal
  | literal_bool : bool -> literal
  | literal_number : number -> literal
  | literal_string : string -> literal.

(** Labels used by break and continue keywords *)

Definition label := string.

(** An optional label:
    [None] refers to "the empty label", and [Some s] 
    refers to a user label with string [s]. *)

Definition label_opt := option label.

(** A set of label, possibly including the empty label. *)

Definition label_set := set label.

(** Strictness flag *)

Definition strictness_flag := bool.

(** Property name in source code *)

Inductive propname :=
  | propname_identifier : string -> propname
  | propname_string : string -> propname
  | propname_number : number -> propname.

(** Grammar of expressions *)

Inductive expr :=
  | expr_this : expr
  | expr_identifier : string -> expr
  | expr_literal : literal -> expr
  | expr_object : list (propname * propbody) -> expr
  | expr_function : option string -> list string -> funcbody -> expr
  | expr_access : expr -> expr -> expr
  | expr_member : expr -> string -> expr
  | expr_new : expr -> list expr -> expr
  | expr_call : expr -> list expr -> expr
  | expr_unary_op : unary_op -> expr -> expr
  | expr_binary_op : expr -> binary_op -> expr -> expr
  | expr_conditional : expr -> expr -> expr -> expr
  | expr_assign : expr -> option binary_op -> expr -> expr

(** Grammar of object properties *)

with propbody :=
  | propbody_val : expr -> propbody
  | propbody_get : funcbody -> propbody
  | propbody_set : list string -> funcbody -> propbody

(** Grammar of function bodies *)

with funcbody :=
  | funcbody_intro : prog -> string -> funcbody
  
(** Grammar of statements *)

with stat :=
  | stat_expr : expr -> stat
  | stat_label : label -> stat -> stat 
  | stat_block : list stat -> stat
  | stat_var_decl : list (string * option expr) -> stat
  | stat_if : expr -> stat -> option stat -> stat
  | stat_do_while : label_set -> stat -> expr -> stat
  | stat_while : label_set -> expr -> stat -> stat
  | stat_with : expr -> stat -> stat
  | stat_throw : expr -> stat
  | stat_return : option expr -> stat
  | stat_break : label_opt -> stat
  | stat_continue : label_opt ->  stat
  | stat_try : stat -> option (string * stat) -> option stat -> stat (* Note: try s1 [catch (x) s2] [finally s3] *)
  | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *)
  | stat_for_in_var : label_set -> string -> option expr -> expr -> stat -> stat (*  Note: for (var x [= e1] in e2) stat *)
  | stat_debugger : stat  
  (* LATER: add do_while *)
  (* LATER: add switch *)

(** Grammar of programs *)

with prog := 
  | prog_intro : strictness_flag -> list element -> prog 

with element :=
  | element_stat : stat -> element
  | element_func_decl : string -> list string -> funcbody -> element.

(** Short names for lists *)

Definition propdefs := list (propname * propbody).

Definition elements := list element.

(** Coercions for grammars *)

Coercion stat_expr : expr >-> stat.


(**************************************************************)
(** ** Identifiers for built-in objects and locations *)

(** Identifiers for builtin maths functions *)

Inductive math_op :=
  | math_op_abs : math_op
  (* LATER: many others *)
  .

(** Identifiers for builtin functions and objects *)

Inductive builtin :=
  
  | builtin_default_get
  | builtin_default_get_own_prop
  | builtin_default_get_prop
  | builtin_default_put
  | builtin_default_can_put
  | builtin_default_has_prop
  | builtin_default_delete
  | builtin_default_default_value
  | builtin_default_define_own_prop

  | builtin_error
  | builtin_range_error
  | builtin_ref_error
  | builtin_syntax_error
  | builtin_type_error

  | builtin_global                    (* location to global object *)
  | builtin_global_eval               (* location to eval function object *)
  | builtin_global_eval_call          (* id for calling eval *)
  (*
  | builtin_global_parse_int
  | builtin_global_parse_int_call
  | builtin_global_parse_float
  | builtin_global_parse_float_call
  *)
  | builtin_global_is_nan            (* location to isNan function object *)
  | builtin_global_is_nan_call       (* id for calling isNan *)
  | builtin_global_is_finite         (* location to isFinite function object *)
  | builtin_global_is_finite_call    (* id for calling isFinite *)

  (* for objects of class Object *)
  | builtin_object
  | builtin_object_new
  | builtin_object_call
  | builtin_object_get_prototype_of      (* location to getPrototypeOf function object *)
  | builtin_object_get_prototype_of_call (* id for calling getPrototypeOf *)
  (* LATER:
    builtin_object_get_own_prop_descriptor
    builtin_object_get_own_prop_descriptor_call
    builtin_object_get_own_prop_name
    builtin_object_get_own_prop_name_call
    builtin_object_create
    builtin_object_create_call
    builtin_object_define_prop
    builtin_object_define_prop_call
    builtin_object_define_properties
    builtin_object_define_properties_call *)
  (*
  | builtin_object_seal
  | builtin_object_seal_call
  | builtin_object_freeze
  | builtin_object_freeze_call
  *)
  | builtin_object_prevent_extensions
  (*
  | builtin_object_prevent_extensions_call
  *)
  | builtin_object_is_sealed
  (*
  | builtin_object_is_sealed_call
  | builtin_object_is_frozen
  | builtin_object_is_frozen_call
  *)  
  | builtin_object_is_extensible
  (*
  | builtin_object_is_extensible_call
  *)
  (* LATER:
  | builtin_object_keys
  | builtin_object_keys_call *)

  | builtin_object_proto
  | builtin_object_proto_to_string
  | builtin_object_proto_to_string_call
  | builtin_object_proto_value_of
  | builtin_object_proto_value_of_call
  (* TODO
  | builtin_object_proto_has_own_prop
  | builtin_object_proto_has_own_prop_call
  *)
  | builtin_object_proto_is_prototype_of
  | builtin_object_proto_is_prototype_of_call
  | builtin_object_proto_prop_is_enumerable
  (* TODO  
  | builtin_object_proto_prop_is_enumerable_call
  *)

  | builtin_function
  | builtin_function_call
  | builtin_function_new
  | builtin_function_proto
  (* Couldn't use the name builtin_function_proto_call for Function.prototype() since there is Function.prototype.call() *)
  | builtin_function_proto_invoked  
  (*
  | builtin_function_proto_to_string
  | builtin_function_proto_apply
  | builtin_function_proto_call
  *)
  
  (* 13.2.3 Unique function object *)
  | builtin_function_throw_type_error

  (* LATER:
  | builtin_function_proto_bind ... etc... *)
  | builtin_array_call
  | builtin_array_new
  | builtin_array_is_array
  | builtin_array_proto
  (* LATER:
  | builtin_array_proto_to_string *)

  | builtin_string_proto
  | builtin_string_call
  | builtin_string_new
  (*
  | builtin_string_proto_to_string
  | builtin_string_proto_value_of
  | builtin_string_proto_char_at
  *)
  (* LATER:
  | builtin_string_proto_char_code_at *)

  | builtin_bool
  | builtin_bool_proto
  | builtin_bool_call
  | builtin_bool_new
  | builtin_bool_proto_to_string
  | builtin_bool_proto_to_string_call
  | builtin_bool_proto_value_of
  | builtin_bool_proto_value_of_call

  | builtin_number
  | builtin_number_call
  | builtin_number_new
  | builtin_number_proto
  | builtin_number_proto_to_string
  | builtin_number_proto_to_string_call
  | builtin_number_proto_value_of
  | builtin_number_proto_value_of_call
  (* LATER:
  | builtin_number_proto_to_fixed
  | builtin_number_proto_to_exponential
  | builtin_number_proto_to_precision
   *)

  | builtin_math
  | builtin_math_function : math_op -> builtin
  
  (* Spec operation ids *)
    
  (* [[Call]] *)

  | builtin_spec_op_function_call      (* 13.2.1 *)  
  | builtin_spec_op_function_bind_call (* 15.3.4.5.1 *) (* TODO *)
  
  (* [[Constructor]] *)
  | builtin_spec_op_function_constructor (* 13.2.2 *)
  | builtin_spec_op_function_bind_constructor (* 15.3.4.5.2 *) (* TODO *)
  
  (* [[HasInstance]] *)
  | builtin_spec_op_function_has_instance      (* 15.3.5.3 *)
  | builtin_spec_op_function_bind_has_instance (* 15.3.4.5.3 *) (* TODO *)
  
  (* [[Get]] *) 
  | builtin_spec_op_object_get (* 8.12.3 *)
  | builtin_spec_op_function_get (* 15.3.5.4 *)
  .


(**************************************************************)
(** ** Representation of values and types (8.1 to 8.5) *)

(** Locations of objects *)

Inductive object_loc :=
  | object_loc_normal : nat -> object_loc
  | object_loc_builtin : builtin -> object_loc.

(** Grammar of primitive values *)

Inductive prim :=
  | prim_undef : prim
  | prim_null : prim
  | prim_bool : bool -> prim
  | prim_number : number -> prim
  | prim_string : string -> prim.

(** Grammar of values *)

Inductive value :=
  | value_prim : prim -> value
  | value_object : object_loc -> value.

(** Grammar of types *)

Inductive type :=
  | type_undef : type
  | type_null : type
  | type_bool : type
  | type_number : type
  | type_string : type
  | type_object : type.

(** Shorthands for [null] and [undef] *)

Notation "'null'" := (value_prim prim_null).
Notation "'undef'" := (value_prim prim_undef).

(** Coercions for primitive and values *)

Coercion prim_bool : bool >-> prim.
Coercion prim_number : JsNumber.number >-> prim.
Coercion prim_string : string >-> prim.
Coercion value_prim : prim >-> value.
Coercion object_loc_builtin : builtin >-> object_loc.
Coercion value_object : object_loc >-> value.


(**************************************************************)
(** ** Representation of property attributes (8.6.1) *)

(** Named data property attributes *)

Record attributes_data := attributes_data_intro {
   attributes_data_value : value;
   attributes_data_writable : bool;
   attributes_data_enumerable : bool;
   attributes_data_configurable : bool }.

(** Named accessor property attributes *)

Record attributes_accessor := attributes_accessor_intro {
   attributes_accessor_get : value;
   attributes_accessor_set : value;
   attributes_accessor_enumerable : bool;
   attributes_accessor_configurable : bool }.

(** Property attributes *)

Inductive attributes := 
  | attributes_data_of : attributes_data -> attributes
  | attributes_accessor_of : attributes_accessor -> attributes.

(** Coercions for property attributes *)

Coercion attributes_data_of : attributes_data >-> attributes.
Coercion attributes_accessor_of : attributes_accessor >-> attributes.


(**************************************************************)
(** ** Representation of property descriptors (8.10) *)

(** Property descriptor *)

Record descriptor := descriptor_intro {
   descriptor_value : option value;
   descriptor_writable : option bool;
   descriptor_get : option value;
   descriptor_set : option value;
   descriptor_enumerable : option bool;
   descriptor_configurable : option bool }.

(** Fully-populated property descriptor (possibly undefined) *)

Inductive full_descriptor :=
  | full_descriptor_undef : full_descriptor
  | full_descriptor_some : attributes -> full_descriptor.

(** Coercion for non-null property descriptors *)

Coercion full_descriptor_some : attributes >-> full_descriptor.


(**************************************************************)
(** ** Representation of environment records and lexical environments (10.2) *)

(** Mutability flags used by declarative environment records *)

Inductive mutability :=
  | mutability_uninitialized_immutable
  | mutability_immutable
  | mutability_nondeletable
  | mutability_deletable.

(** Representation of a declarative environment records *)

Definition decl_env_record :=
  Heap.heap string (mutability * value).

(** Provide-this flag used by object environment records *)

Definition provide_this_flag := bool.

(** Representation of environment records *)

Inductive env_record :=
  | env_record_decl : decl_env_record -> env_record
  | env_record_object : object_loc -> provide_this_flag -> env_record.

(** Coercion for declarative environment records *)

Coercion env_record_decl : decl_env_record >-> env_record.

(** Pointer on an environment record *)

Definition env_loc := nat.

(** The pre-allocated address of the global environment. *)

Parameter env_loc_global_env_record : env_loc.

(** Representation of lexical environments *)

Definition lexical_env := list env_loc.


(**************************************************************)
(** ** Representation of execution contexts (10.3) *)

(** Representation of execution contexts *)

Record execution_ctx := execution_ctx_intro {
   execution_ctx_lexical_env : lexical_env;
   execution_ctx_variable_env : lexical_env;
   execution_ctx_this_binding : value;
   execution_ctx_strict : strictness_flag }.


(**************************************************************)
(** ** Representation of references (8.7) *)

(** Representation of the names of a property *)

Definition prop_name := string.

(** Representation of the base value of a reference *)

Inductive ref_base_type :=
  | ref_base_type_value : value -> ref_base_type
  | ref_base_type_env_loc : env_loc -> ref_base_type.

(** Representation of the reference (specification) type *)

Record ref := ref_intro {
  ref_base : ref_base_type;
  ref_name : prop_name;
  ref_strict : bool }.


(**************************************************************)
(** ** Representation of objects (8.6.2) *)

(** Representation of the class name *)

Definition class_name := string.

(** Representation of the map from properties to attributes *)

Definition object_properties_type :=
  Heap.heap prop_name attributes.

(** Representation of objects *)

Record object := object_intro {
   object_proto_ : value;
   object_class_ : class_name;
   object_extensible_ : bool;
   object_prim_value_ : option value;
   object_properties_ : object_properties_type;
   object_get_ : builtin;
   object_get_own_prop_ : builtin;
   object_get_prop_ : builtin;
   object_put_ : builtin;
   object_can_put_ : builtin;
   object_has_prop_ : builtin;
   object_delete_ : builtin;
   object_default_value_ : builtin;
   object_define_own_prop_ : builtin;
   object_construct_ : option builtin;
   object_call_ : option builtin;
   object_has_instance_ : option builtin;
   object_scope_ : option lexical_env;
   object_formal_parameters_ : option (list string);
   object_code_ : option funcbody;
   object_target_function_ : option object_loc;
   object_bound_this_ : option value;
   object_bound_args_ : option (list value);
   object_parameter_map_ : option object_loc
   (* LATER: match for regular expression matching *)
   }.


(**************************************************************)
(** ** Representation of the state *)

(** Representation of the state, as a heap storing objects,
    a heap storing environment records, and a freshness generator
    -- TODO: store the fresh locations into a wrapper around LibHeap *)

Record state := state_intro {
   state_object_heap : Heap.heap object_loc object;
   state_env_record_heap : Heap.heap env_loc env_record;
   state_fresh_locations : stream nat }.


(**************************************************************)
(**************************************************************)
(****************************************************************)
(** ** Definition of outcomes (8.9) *)

(** Kind of results *)

Inductive restype :=
  | restype_normal
  | restype_break
  | restype_continue
  | restype_return
  | restype_throw.

(** Kind of values carried by a result *)

Inductive resvalue :=
  | resvalue_empty : resvalue
  | resvalue_value : value -> resvalue
  | resvalue_ref : ref -> resvalue.

Coercion resvalue_value : value >-> resvalue.
Coercion resvalue_ref : ref >-> resvalue.

(** Representation of a result as a triple *)

Inductive res := res_intro {
  res_type : restype;
  res_value : resvalue;
  res_label : label_opt }.
  
Definition abrupt_res R :=
  res_type R <> restype_normal.

(** Smart constructors for type [res] *)

Coercion res_ref r := res_intro restype_normal r None.
Coercion res_val v := res_intro restype_normal v None.
Coercion res_normal rv := res_intro restype_normal rv None.

Definition res_empty := res_intro restype_normal resvalue_empty None.
Definition res_break labo := res_intro restype_break resvalue_empty labo.
Definition res_continue labo := res_intro restype_continue resvalue_empty labo.
Definition res_return v := res_intro restype_return v None.
Definition res_throw v := res_intro restype_throw v None.

(** Outcome of an evaluation: divergence or termination *)

Inductive out :=
  | out_div : out
  | out_ter : state -> res -> out.


(**************************************************************)
(**************************************************************)
(****************************************************************)
(** ** Auxiliarly data structures used for the semantics *)

(** Representation of function code -- TODO: seems to be deprecated *)

Inductive funccode :=
  | funccode_code : prog -> funccode  (* TODO: this should probably be of type funcbody -> funccode *)
  | funccode_builtin : builtin -> funccode.

Coercion funccode_builtin : builtin >-> funccode.

(** Representation of a function declaration *)

Record funcdecl := funcdecl_intro {
   funcdecl_name : string;
   funcdecl_parameters : list string;
   funcdecl_body : funcbody }.


