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
(** ** Representation of syntax *)

(* Unary operator *)

Inductive unary_op :=
  | unary_op_not
  | unary_op_delete
  | unary_op_typeof
  | unary_op_pre_incr
  | unary_op_post_incr
  | unary_op_pre_decr
  | unary_op_post_decr
  | unary_op_void.

(** Binary operators *)

Inductive binary_op :=
  | binary_op_add
  | binary_op_mult
  | binary_op_div
  | binary_op_equal
  (* Daniele 
  | binary_op_not_equal
  | binary_op_strict_equal
  | binary_op_strict_not_equal
  *)
  | binary_op_instanceof
  | binary_op_in
  | binary_op_and
  | binary_op_or.

(** Grammar of literals *)

Inductive literal :=
  | literal_null : literal
  | literal_bool : bool -> literal
  | literal_number : number -> literal
  | literal_string : string -> literal.

(** Labels used by break and continue keywords *)

Definition loop_label := string.

(* TODO: define a type loop_label_opt for option loop_label *)

(** Strictness flag *)

Definition strictness_flag := bool.

(** Grammar of expressions *)

Inductive expr :=
  | expr_this : expr
  | expr_variable : string -> expr
  | expr_literal : literal -> expr
  | expr_object : list (string * expr) -> expr
  | expr_function : option string -> list string -> prog -> expr
  | expr_access : expr -> expr -> expr
  | expr_member : expr -> string -> expr
  | expr_new : expr -> list expr -> expr
  | expr_call : expr -> list expr -> expr
  | expr_unary_op : unary_op -> expr -> expr
  | expr_binary_op : expr -> binary_op -> expr -> expr
  | expr_assign : expr -> option binary_op -> expr -> expr

(** Grammar of statements *)

(* -->TODO: general labelled statements *)
(* TODO: is our representation of labels faithful to the spec in 12.0 *)

with stat :=
(* -->TODO: var x,y;  is it equivalent to var x; var y ? *)
  | stat_expr : expr -> stat
  | stat_seq : stat -> stat -> stat 
  | stat_var_decl : string -> option expr -> stat
  | stat_if : expr -> stat -> option stat -> stat
  | stat_while : (* TODO: option loop_label -> *) expr -> stat -> stat
  | stat_with : expr -> stat -> stat
  | stat_throw : expr -> stat
  | stat_return : option expr -> stat
  | stat_break : (* TODO: option loop_label -> *) stat
  | stat_continue : (* TODO: option loop_label -> *) stat
  | stat_try : stat -> option (string * stat) -> option stat -> stat  
               (* try s1 [catch (x) s2] [finally s3] *)
  | stat_skip (* for semi-column *)
  | stat_for_in : expr -> expr -> stat -> stat (* for (e1 in e2) stat *)
  | stat_for_in_var : string -> option expr -> expr -> stat -> stat (* for (var x [= e1] in e2) stat *)
  (* todo: factorize the two *)
(* TODO: missing do_while and for *)
(* TODO: missing switch *)

(* TODO: note the invariant somewhere:
   - try must have either catch or finally
   - with statement cannot be in strict mode
*)

(** Grammar of programs *)

with prog :=
  | prog_stat : stat -> prog
  | prog_seq : prog -> prog -> prog 
  (* TODO: use function_declaration type *)
  | prog_function_decl : string -> list string -> prog -> prog.
  (* TODO:  Add prog_use_strict : prog -> prog. *)


(** Coercions for grammars *)

Coercion stat_expr : expr >-> stat.
Coercion prog_stat : stat >-> prog.

Record function_declaration := function_declaration_intro {
   fd_name : string;
   fd_parameters : list string;
   fd_code : prog }.
   
(* TODO *)
Parameter function_body_is_strict : prog -> bool.


(**************************************************************)
(** ** Identifiers for built-in objects and locations *)

(** Identifiers for builtin maths functions *)

Inductive math_op :=
  | math_op_abs : math_op
  (* LATER: many others *)
  .

(** Identifiers for builtin functions and objects *)

Inductive builtin := 

  | builtin_error
  | builtin_range_error
  | builtin_ref_error
  | builtin_syntax_error
  | builtin_type_error

  | builtin_global
  | builtin_global_eval
  (*
  | builtin_global_parse_int
  | builtin_global_parse_float
  *)
  | builtin_global_is_nan
  (*
  | builtin_global_is_finite
  *)

  | builtin_object
  | builtin_object_new
  | builtin_object_call
  | builtin_object_get_prototype_of
  (* LATER: 
    builtin_object_get_own_property_descriptor
    builtin_object_get_own_property_name
    builtin_object_create
    builtin_object_define_property
    builtin_object_define_properties *)
  (*
  | builtin_object_seal
  | builtin_object_freeze
  | builtin_object_prevent_extensions
  | builtin_object_is_sealed
  | builtin_object_is_frozen
  | builtin_object_is_extensible
  *)
  (* LATER: 
    builtin_object_keys *)

  | builtin_object_proto
  | builtin_object_proto_to_string
  | builtin_object_proto_value_of
  | builtin_object_proto_has_own_property
  | builtin_object_proto_is_prototype_of
  | builtin_object_proto_property_is_enumerable

  | builtin_function
  | builtin_function_call
  | builtin_function_new
  | builtin_function_proto
  (* 13.2.3 Unique function object *)
  | builtin_function_throw_type_error
  (*
  | builtin_function_proto_apply
  | builtin_function_proto_call
  | builtin_function_proto_to_string
  *)

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

  | builtin_bool_call
  | builtin_bool_new
  | builtin_bool_proto_to_string
  | builtin_bool_proto_value_of  

  | builtin_number_call  
  | builtin_number_new
  | builtin_number_proto
  | builtin_number_proto_to_string
  | builtin_number_proto_value_of  
  (* LATER:
  | builtin_number_proto_to_fixed
  | builtin_number_proto_to_exponential
  | builtin_number_proto_to_precision
   *)

  | builtin_math
  | builtin_math_function : math_op -> builtin 
  .


(**************************************************************)
(** ** Representation of values and types *)

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

(** Shorthands for [null] and [undef] *)

Notation "'null'" := (value_prim prim_null).
Notation "'undef'" := (value_prim prim_undef).

(** Grammar of types *)

Inductive type :=
  | type_undef : type
  | type_null : type
  | type_bool : type  
  | type_number : type
  | type_string : type
  | type_object : type.

(** Coercions for primitive and values *)

Coercion prim_bool : bool >-> prim.
Coercion prim_number : JsNumber.number >-> prim.
Coercion prim_string : string >-> prim.
Coercion value_prim : prim >-> value.
Coercion object_loc_builtin : builtin >-> object_loc.
Coercion value_object : object_loc >-> value.


(**************************************************************)
(** ** Representation of execution contexts *)

(** Representation of the names of a property *)

Definition prop_name := string.

(** Property attributes *)

Record prop_attributes := prop_attributes_intro {
   prop_attributes_value : option value;
   prop_attributes_writable : option bool;
   prop_attributes_get : option value;
   prop_attributes_set : option value;
   prop_attributes_enumerable : option bool;
   prop_attributes_configurable : option bool }.

(** Possibly-null property descriptor *)

Inductive prop_descriptor := 
  | prop_descriptor_undef : prop_descriptor
  | prop_descriptor_some : prop_attributes -> prop_descriptor.

(** Coercion for non-null property descriptors *)

Coercion prop_descriptor_some : prop_attributes >-> prop_descriptor.

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

(** Representation of execution contexts *)

Record execution_ctx := execution_ctx_intro {
   execution_ctx_lexical_env : lexical_env;
   execution_ctx_variable_env : lexical_env;
   execution_ctx_this_binding : value;
   execution_ctx_strict : strictness_flag }.


(**************************************************************)
(** ** Representation of references *)

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
(** ** Representation of objects *)

(** Representation of the class name *)

Definition class_name := string.

(** Representation of function code *)

Inductive function_code :=
  | function_code_code : prog -> function_code
  | function_code_builtin : builtin -> function_code.

(** Representation of the map from properties to attributes *)

Definition object_properties_type := 
  Heap.heap prop_name prop_attributes.

(** Representation of objects *)

Record object := object_intro {
   object_proto_ : value;
   object_class_ : class_name;
   object_extensible_ : bool;
   object_properties_ : object_properties_type;
   object_prim_value_ : option value;
   object_construct_ : option function_code;
   object_call_ : option function_code;
   object_has_instance_ : option builtin;
   object_scope_ : option lexical_env;
   object_formal_parameters_ : option (list string);
   object_code_ : option function_code;
   object_target_function_ : option object_loc; 
   object_bound_this_ : option value; 
   object_bound_args_ : option (list value); 
   object_parameter_map_ : option object_loc 
   (* LATER: match for regular expression matching *)   
   }.

(** Special modes for [get_own_property] and [set_own_property] *)

Inductive object_special :=
  | object_special_default 
  | object_special_string
  | object_special_array.


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
(** ** Definition of outcomes *)

(** Normal return value of an expression *)

Inductive ret :=
  | ret_value : value -> ret
  | ret_ref : ref -> ret.

(** Result of an evaluation *)

Inductive res :=
  | res_normal : ret -> res
  | res_break : option loop_label -> res
  | res_continue : option loop_label -> res
  | res_return : ret -> res (* todo : is it value -> res *)
  | res_throw : value -> res.

(** Outcome of an evaluation *)

Inductive out :=
  | out_div : out
  | out_ter : state -> res -> out.

(** Coercions *)

Coercion ret_value : value >-> ret.
Coercion ret_ref : ref >-> ret.
Coercion res_normal : ret >-> res.

(* <informal> Implicit Type o : out_*  *)


(**************************************************************)
(** ** TODO:  Move those functions to Preliminary once the file defined. *)

(**************************************************************)
(** ** Auxiliary functions on values and types *)

(** Convert a literal into a primitive *) 

Definition convert_literal_to_prim (i:literal) :=
  match i with
  | literal_null => prim_null
  | literal_bool b => prim_bool b
  | literal_number n => prim_number n 
  | literal_string s => prim_string s
  end.

(** Convert a literal into a value *) 

Definition convert_literal_to_value (i:literal) :=
  value_prim (convert_literal_to_prim i).

(** Specification method that returns the type of a value *)

Definition type_of v :=
  match v with
  | value_prim w =>
     match w with
     | prim_undef => type_undef
     | prim_null => type_null
     | prim_bool _ => type_bool
     | prim_number _ => type_number
     | prim_string _ => type_string
     end
  | value_object _ => type_object
  end.

(** Definition of the "SameValue" algorithm *)

Definition value_same v1 v2 :=
  let T1 := type_of v1 in
  let T2 := type_of v2 in
  If T1 <> T2 then False else
  match T1 with
  | type_undef => True
  | type_null => True
  | type_number =>
      If    v1 = (prim_number JsNumber.nan) 
         /\ v2 = (prim_number JsNumber.nan) then True
      else If    v1 = (prim_number JsNumber.zero) 
              /\ v2 = (prim_number JsNumber.neg_zero) then False
      else If    v1 = (prim_number JsNumber.neg_zero) 
              /\ v2 = (prim_number JsNumber.zero) then False
      else (v1 = v2)
  | type_string => 
      v1 = v2
  | type_bool => 
      v1 = v2
  | type_object => 
      v1 = v2
  end.

(**************************************************************)
(** ** Auxiliary definitions for reduction of [get_own_property]  *)

(** The 4 following definitions are used to define when
    a property descriptor contains another one. *)

Definition if_some_then_same (A:Type) F (oldf newf : option A) :=
  match newf, oldf with
  | Some v1, Some v2 => F v1 v2
  | Some v1, None => False
  | None, _ => True
  end.

Definition if_some_value_then_same :=
  if_some_then_same value_same.

Definition if_some_bool_then_same :=
  if_some_then_same (A := bool)eq.

Definition prop_attributes_contains oldpf newpf := 
  match oldpf, newpf with 
  | prop_attributes_intro ov ow og os oe oc, 
    prop_attributes_intro nv nw ng ns ne nc =>
       if_some_value_then_same ov nv
    /\ if_some_bool_then_same ow nw
    /\ if_some_value_then_same og ng
    /\ if_some_value_then_same os ns
    /\ if_some_bool_then_same oe ne
    /\ if_some_bool_then_same oc nc
  end.

(** The 2 following definitions are used to define what
    it means to copy the defined attributes of a property 
    descriptors into another descriptor. *)

Definition option_transfer (A:Type) (oldopt newopt : option A) :=
  match newopt with
  | None => oldopt
  | _ => newopt
  end.

  (* TEMP: Alternative definition:
  match newopt,oldopt with
  | Some v, _ => Some v
  | _, _ => oldopt
  end.*)

Definition prop_attributes_transfer oldpf newpf := 
  match oldpf, newpf with 
  | prop_attributes_intro ov ow og os oe oc, 
    prop_attributes_intro nv nw ng ns ne nc =>
    prop_attributes_intro 
      (option_transfer ov nv)
      (option_transfer ow nw)
      (option_transfer og ng)
      (option_transfer os ns)
      (option_transfer oe ne)
      (option_transfer oc nc)
  end.

(** The 8 following definitions are used to describe the
    cases in which the define_own_property specification method 
    performs an illegal operation. *)

Definition some_compare (A:Type) F (o1 o2 : option A) :=
  match o1, o2 with
  | Some v1, Some v2 => F v1 v2
  | _, _ => False
  end.
  
Definition some_not_same_value :=
   some_compare (fun v1 v2 => ~ value_same v1 v2).
   
Definition some_not_same_bool :=
   some_compare (fun b1 b2 : bool (* TODO:  Remove this type annotation (once moved in the file Preliminary) *) => b1 <> b2).   
  
Definition change_enumerable_attributes_on_non_configurable oldpf newpf : Prop :=
     prop_attributes_configurable oldpf = Some false 
  /\ (   prop_attributes_configurable newpf = Some true 
      \/ some_not_same_bool (prop_attributes_enumerable newpf) (prop_attributes_enumerable oldpf)).

Definition change_writable_on_non_configurable oldpf newpf : Prop :=
     prop_attributes_writable oldpf = Some false 
  /\ prop_attributes_writable newpf = Some true.
    
Definition change_value_on_non_writable oldpf newpf : Prop :=
     prop_attributes_writable oldpf = Some false
  /\ some_not_same_value (prop_attributes_value newpf) (prop_attributes_value oldpf).
  
Definition change_data_attributes_on_non_configurable oldpf newpf : Prop :=
     change_writable_on_non_configurable oldpf newpf
  \/ change_value_on_non_writable oldpf newpf.

Definition change_accessor_on_non_configurable oldpf newpf : Prop :=
     prop_attributes_configurable oldpf = Some false 
  /\ (   some_not_same_value (prop_attributes_set newpf) (prop_attributes_set oldpf)
      \/ some_not_same_value (prop_attributes_get newpf) (prop_attributes_get oldpf)).

