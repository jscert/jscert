Set Implicit Arguments.
Require Export Shared.
Require Export Ascii String.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc
  LibHeap LibStream LibListSorted.
Module Heap := HeapGen (LibHeap.HeapList).
Require JsNumber.
Notation "'number'" := (JsNumber.number).


(* LATER (ARTHUR): There seems to be problems with modules and I've temporarily added
  this lemma to avoid those troubles, but there surely is a better
  solution for it. -- Martin. *)
Lemma Heap_binds_func : forall (K V : Type) `{Comparable K}
  (h : Heap.heap K V) (k : K) (v v' : V),
  Heap.binds h k v -> Heap.binds h k v' -> v = v'.
Proof.
  introv C B1 B2. rewrite Heap.binds_equiv_read_option in B1,B2.
  rewrite B1 in B2. inverts~ B2.
Qed.


(**************************************************************)

(* [heap_keys_as_list h ks] holds if the list [ks] is a
   permutation of the set of keys of the map [h]. *)

Definition heap_keys_as_list A B (h : Heap.heap A B) l :=
  permut (keys (Heap.to_list h)) l.


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

(** Labels literals used by break and continue keywords,
    including the special "empty" label. *)

Inductive label :=
   | label_empty : label
   | label_string : string -> label.

(** A set of labels, possibly including the empty label. *)

Definition label_set := list label.

(** Strictness flag *)

Definition strictness_flag := bool.
Definition strictness_true : strictness_flag := true.
Definition strictness_false : strictness_flag := false.

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

  (* _ARRAYS_ : support for processing arrays, based on parser_syntax.ml *)
  | expr_array : list (option expr) -> expr

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
(* LATER: An explanation of these additionnal [label_set] would be welcomed. *)

with stat := 
  | stat_expr : expr -> stat
  | stat_label : string -> stat -> stat
  | stat_block : list stat -> stat
  | stat_var_decl : list (string * option expr) -> stat
  | stat_if : expr -> stat -> option stat -> stat
  | stat_do_while : label_set -> stat -> expr -> stat
  | stat_while : label_set -> expr -> stat -> stat
  | stat_with : expr -> stat -> stat
  | stat_throw : expr -> stat
  | stat_return : option expr -> stat
  | stat_break : label -> stat
  | stat_continue : label ->  stat
  | stat_try : stat -> option (string * stat) -> option stat -> stat (* Note: try s1 [catch (x) s2] [finally s3] *)
  | stat_for : label_set -> option expr -> option expr -> option expr -> stat -> stat (* Note: for (e1; e2; e3) stat *)
  | stat_for_var : label_set -> list (string * option expr) -> option expr -> option expr -> stat -> stat (* Note: for (var ...; e2; e3) stat *)
  | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *)
  | stat_for_in_var : label_set -> string -> option expr -> expr -> stat -> stat (*  Note: for (var x [= e1] in e2) stat *)
  | stat_debugger : stat
  | stat_switch : label_set -> expr -> switchbody -> stat

with switchbody :=
  | switchbody_nodefault : list switchclause -> switchbody
  | switchbody_withdefault : list switchclause -> list stat -> list switchclause -> switchbody

with switchclause :=
  | switchclause_intro : expr -> list stat -> switchclause

(** Grammar of programs *)

with prog :=
  | prog_intro : strictness_flag -> list element -> prog

(** Grammar of program elements *)

with element :=
  | element_stat : stat -> element
  | element_func_decl : string -> list string -> funcbody -> element.

(** Short names for lists *)

Definition propdefs := list (propname * propbody).

Definition elements := list element.

(** Representation of a function declaration
    (used only for the description of the semantics) *)

Record funcdecl := funcdecl_intro {
   funcdecl_name : string;
   funcdecl_parameters : list string;
   funcdecl_body : funcbody }.

(** Coercions for grammars *)

Coercion stat_expr : expr >-> stat.
Coercion label_string : string >-> label.


(**************************************************************)
(** ** Identifiers for built-in objects and locations *)

(** Identifiers for builtin maths functions *)

Inductive mathop :=
  | mathop_abs : mathop
  (* LATER: many others *)
  .

(** Identifiers for native error objects  (* 15.11.6 *) *)

Inductive native_error :=
  | native_error_eval
  | native_error_range
  | native_error_ref
  | native_error_syntax
  | native_error_type
  | native_error_uri.

(** Identifiers for objects pre-allocated in the initial heap *)

Inductive prealloc :=
  | prealloc_global (* not callable *)
  | prealloc_global_eval
  | prealloc_global_parse_int
  | prealloc_global_parse_float
  | prealloc_global_is_finite
  | prealloc_global_is_nan
  | prealloc_global_decode_uri
  | prealloc_global_decode_uri_component
  | prealloc_global_encode_uri
  | prealloc_global_encode_uri_component
  | prealloc_object
  | prealloc_object_get_proto_of      (* location to getPrototypeOf function object *)
  | prealloc_object_get_own_prop_descriptor
  | prealloc_object_get_own_prop_name  (* LATER: support *)
  | prealloc_object_create
  | prealloc_object_define_prop
  | prealloc_object_define_props
  | prealloc_object_seal
  | prealloc_object_freeze
  | prealloc_object_prevent_extensions
  | prealloc_object_is_sealed
  | prealloc_object_is_frozen
  | prealloc_object_is_extensible
  | prealloc_object_keys  (* LATER: support *)
  | prealloc_object_keys_call  (* LATER: support *)
  | prealloc_object_proto
  | prealloc_object_proto_to_string
  | prealloc_object_proto_value_of
  | prealloc_object_proto_has_own_prop (* LATER: support *)
  | prealloc_object_proto_is_prototype_of
  | prealloc_object_proto_prop_is_enumerable
  | prealloc_function
  | prealloc_function_proto
  | prealloc_function_proto_to_string
  | prealloc_function_proto_apply
  | prealloc_function_proto_call
  | prealloc_function_proto_bind (* LATER: support this and others *)
  | prealloc_bool
  | prealloc_bool_proto
  | prealloc_bool_proto_to_string
  | prealloc_bool_proto_value_of
  | prealloc_number
  | prealloc_number_proto
  | prealloc_number_proto_to_string
  | prealloc_number_proto_value_of
  | prealloc_number_proto_to_fixed (* LATER: support *)
  | prealloc_number_proto_to_exponential (* LATER: support *)
  | prealloc_number_proto_to_precision (* LATER: support *)
  | prealloc_array
  | prealloc_array_is_array
  | prealloc_array_proto
  | prealloc_array_proto_to_string 
  | prealloc_array_proto_join
  | prealloc_array_proto_pop
  | prealloc_array_proto_push
  | prealloc_string
  | prealloc_string_proto
  | prealloc_string_proto_to_string (* LATER: support *)
  | prealloc_string_proto_value_of (* LATER: support *)
  | prealloc_string_proto_char_at (* LATER: support *)
  | prealloc_string_proto_char_code_at (* LATER: support *)
  | prealloc_math (* not callable *)
  | prealloc_mathop : mathop -> prealloc
  | prealloc_date
  | prealloc_regexp
  | prealloc_error (* 15.11 *)
  | prealloc_error_proto (* 15.11.3.1 *)
  | prealloc_native_error : native_error -> prealloc (* 15.11.6 *)
  | prealloc_native_error_proto : native_error -> prealloc (* 15.11.7.7 *) (* not callable *)
  | prealloc_error_proto_to_string
  | prealloc_throw_type_error (* 13.2.3 *)
  | prealloc_json (* not callable *)
  .

(* Identifiers for "Callable" methods *)

Inductive call := (* Note: could be named [builtin_call] *)
  | call_default  (* 13.2.1 *)
  | call_after_bind (* 15.3.4.5.1 *)
  | call_prealloc : prealloc -> call. (* all are functions except those tagged not callable *)

Coercion call_prealloc : prealloc >-> call.
Coercion prealloc_native_error : native_error >-> prealloc.

(** Identifiers for "Construct" methods *)

Inductive construct := (* Note: could be named [builtin_construct] *)
  | construct_default (* 13.2.2 *)
  | construct_after_bind (* 15.3.4.5.2 *) 
  | construct_prealloc : prealloc -> construct.
    (* only the ones below are actually used by construct_prealloc
      | construct_object
      | construct_function
      | construct_bool
      | construct_number
      | construct_array
      | construct_string
      | construct_error
      | construct_range_error
      | construct_ref_error
      | construct_syntax_error
      | construct_type_error
      | construct_throw_type_error
    *)

Coercion construct_prealloc : prealloc >-> construct.

(** Identifiers for "HasInstance" methods *)

Inductive builtin_has_instance :=
  | builtin_has_instance_function (* 15.3.5.3 *)
  | builtin_has_instance_after_bind. (* 15.3.4.5.3 *)  (* LATER: support *)

(** Identifiers for "Get" methods *)

Inductive builtin_get :=
  | builtin_get_default (* 8.12.3 *)
  | builtin_get_function (* 15.3.5.4 *)
  | builtin_get_args_obj. (* 10.6 *)
  (* LATER: string and array *)

(** Identifiers for "GetOwnProperty" methods *)

Inductive builtin_get_own_prop :=
  | builtin_get_own_prop_default
  | builtin_get_own_prop_args_obj
  | builtin_get_own_prop_string.

(** Identifiers for "GetProperty" methods *)

Inductive builtin_get_prop :=
  | builtin_get_prop_default.

(** Identifiers for "Put" methods *)

Inductive builtin_put :=
  | builtin_put_default.
  (* LATER: string and array *)

(** Identifiers for "CanPut" methods *)

Inductive builtin_can_put :=
  | builtin_can_put_default.
  (* LATER: string and array *)

(** Identifiers for "HasProperty" methods *)

Inductive builtin_has_prop :=
  | builtin_has_prop_default.
  (* LATER: string and array *)

(** Identifiers for "Delete" methods *)

Inductive builtin_delete :=
  | builtin_delete_default
  | builtin_delete_args_obj.
  (* LATER: string and array *)

(** Identifiers for "DefaultValue" methods *)

Inductive builtin_default_value :=
  | builtin_default_value_default.
  (* LATER: date *)

(** Identifiers for "DefineOwnProp" methods *)

Inductive builtin_define_own_prop :=
  | builtin_define_own_prop_default
  (* ARRAYS *)
  | builtin_define_own_prop_array
  | builtin_define_own_prop_args_obj.
  (* LATER: string *)


(**************************************************************)
(** ** Representation of values and types (8.1 to 8.5) *)

(** Locations of objects *)

Inductive object_loc :=
  | object_loc_normal : nat -> object_loc
  | object_loc_prealloc : prealloc -> object_loc.

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
Coercion object_loc_prealloc : prealloc >-> object_loc.
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


(**************************************************************)
(** Representation of objects *)

Record object := object_intro {
   object_proto_ : value;
   object_class_ : class_name;
   object_extensible_ : bool;
   object_prim_value_ : option value;
   object_properties_ : object_properties_type;
   object_get_ : builtin_get;
   object_get_own_prop_ : builtin_get_own_prop;
   object_get_prop_ : builtin_get_prop;
   object_put_ : builtin_put;
   object_can_put_ : builtin_can_put;
   object_has_prop_ : builtin_has_prop;
   object_delete_ : builtin_delete;
   object_default_value_ : builtin_default_value;
   object_define_own_prop_ : builtin_define_own_prop;
   object_construct_ : option construct;
   object_call_ : option call ;
   object_has_instance_ : option builtin_has_instance;
   object_scope_ : option lexical_env;
   object_formal_parameters_ : option (list string);
   object_code_ : option funcbody;
   object_target_function_ : option object_loc;
   object_bound_this_ : option value;
   object_bound_args_ : option (list value);
   object_parameter_map_ : option object_loc }.

   (* LATER: match for regular expression matching *)

(**************************************************************)
(* A type of "events" that can be used to pin down the semantics of
for-in. There is one case for each sort of event that can change the
behaviour of an ongoing enumeration. *)

Inductive event := delete_event: object_loc -> prop_name -> option object_loc -> event
                 | mutateproto_event: object_loc
                                      -> list (object_loc * prop_name)
                                      -> list (object_loc * prop_name)
                                      -> event
                 | enumchange_event: object_loc -> prop_name -> event.


(**************************************************************)
(** ** Representation of the state *)

(** Representation of the state, as a heap storing objects,
    a heap storing environment records, and a freshness generator *)
   (* LATER : store the fresh locations into a wrapper around LibHeap *)

Record state := state_intro {
   state_object_heap : Heap.heap object_loc object;
   state_env_record_heap : Heap.heap env_loc env_record;
   state_fresh_locations : stream nat;
   state_event_list : list event }.


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

Record res := res_intro {
  res_type : restype;
  res_value : resvalue;
  res_label : label }.

Definition abrupt_res R :=
  res_type R <> restype_normal.

(** Smart constructors for results *)

(* LATER :  as there are no more implicit type in this file, those three functions
   are exactly the same, taking a resvalue as an argument.  I've fixed the problem
   by annotating the first two, but maybe we should just remove them to avoid
   ambiguous paths. *)

Coercion res_ref (r : ref) := res_intro restype_normal r label_empty.
Coercion res_val (v : value) := res_intro restype_normal v label_empty.
Coercion res_normal rv := res_intro restype_normal rv label_empty.

Definition res_empty := res_intro restype_normal resvalue_empty label_empty.
Definition res_break labo := res_intro restype_break resvalue_empty labo.
Definition res_continue labo := res_intro restype_continue resvalue_empty labo.
Definition res_return v := res_intro restype_return v label_empty.
Definition res_throw v := res_intro restype_throw v label_empty.

(** Outcome of an evaluation: divergence or termination *)

Inductive out :=
  | out_div : out
  | out_ter : state -> res -> out.

(** Special outcome used by specification operations, i.e.
    specification-level functions which do not produce any
    value, but only perform side effects. *)

Definition out_void S := out_ter S res_empty.

(** Internal functions may return values other than JS results,
    or may trigger JS exceptions, or diverge. The type
    [specret A] accounts for such results: [specret_val S a]
    describes a normal result as a pair of a heap [S] and a
    value [a] of type [A], while [specret_out o] describes
    an abrupt behavior [o]. *)

Inductive specret (T : Type) :=
  | specret_val : state -> T -> specret T
  | specret_out : out -> specret T.

Implicit Arguments specret_val [[T]].
Implicit Arguments specret_out [[T]].

(** [ret S a] is a shorthand for [specret_val S a] *)

Definition ret {T} S (a:T) := specret_val S a.
Implicit Arguments ret [[T]].

(** [ret_void S] is a shorthand for [specret_val S tt],
    used by specifications functions that do no return any value.  *)

Definition ret_void S := specret_val S tt.


(**************************************************************)
(** ** Auxiliary definition for DeclarationBindingInstantiation *)

(** A code originates either from a function body, from global
    code, or from the argument of a call to eval. *)

Inductive codetype :=
  | codetype_func : codetype
  | codetype_global : codetype
  | codetype_eval : codetype.


