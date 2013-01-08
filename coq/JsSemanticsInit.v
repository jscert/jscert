Set Implicit Arguments.
Require Export JsSemanticsDefs.

(* TODO: move *)

Coercion function_code_builtin : builtin >-> function_code.

(* TODO:*)

Coercion JsNumber.of_int : Z >-> JsNumber.number.
  



(**************************************************************)
(** ** Implicit Types -- copied from JsSemanticsDefs *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type s : string.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type T : type.

Implicit Type x : prop_name.
Implicit Type m : mutability. 
Implicit Type A : prop_attributes.
Implicit Type An : prop_descriptor.
Implicit Type L : env_loc. 
Implicit Type E : env_record. 
Implicit Type D : decl_env_record.
Implicit Type X : lexical_env. 
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(**************************************************************)
(** Common shorthands *)


(** Shorthand notation for building a property attributes 
    that is non writable, non configurable and non enumerable. *)

Definition prop_attributes_for_global_object v :=
   prop_attributes_create_data v true false true.

(** Shorthand notation for building a property attributes 
    that is non writable, non configurable and non enumerable. *)

Notation "'attrib_constant'" := prop_attributes_create_data_constant.

(** Shorthand notation for building a property attributes 
    that is non writable, non configurable and non enumerable. *)

Notation "'attrib_native'" := prop_attributes_for_global_object.

(* TODO: might not need the above two notations *)

(** Builds an object with all optional fields to None
    and with extensible set to true *)

Definition object_create_builtin vproto sclass P :=
  object_create vproto sclass true P.

(** Builds a native object, with [builtin_function_proto]
    as prototype, and a length property. *)

Definition object_create_builtin_common length P :=
  let sclass := "Function" in
  let P' := Heap.write P "length" (attrib_constant length) in
  object_create_builtin builtin_function_proto sclass P'.

(** Builds a native function object, like in the above function
    but with only a Call method implemented by builtin code. *)

Definition object_create_builtin_function builtin_call length P :=
  let O := object_create_builtin_common length P in
  object_with_invokation O None (Some builtin_call) None.

(** Builds a native constructor object, with a Call method and
    a Construct method implemented by builtin code. *)

Definition object_create_builtin_constructor builtin_call builtin_construct length P :=
  let O := object_create_builtin_common length P in
  object_with_invokation O (Some builtin_construct) (Some builtin_call) None.

(** Shorthand to extend a heap with a native method *)

Definition write_native P name builtin :=
  Heap.write P name (attrib_native (value_object builtin)).

(** Shorthand to extend a heap with a constant *)

Definition write_constant P name value :=
  Heap.write P name (attrib_constant value).


(**************************************************************)
(** Global object *)

(** Implementation-dependent values for prototype and class fields
    of the global object *)

Parameter object_builtin_global_proto : value.
Parameter object_builtin_global_class : string.

(** Properties of the global object *)

Definition object_builtin_global_properties :=
  let P := Heap.empty in
  let P := write_constant P "NaN" JsNumber.nan in
  let P := write_constant P "Infinity" JsNumber.infinity in
  let P := write_constant P "undefined" undef in
  let P := write_native P "eval" builtin_global_eval in
  let P := write_native P "isNan" builtin_global_is_nan in
  (* TODO: many other functions to insert here *)
  let P := write_native P "Object" builtin_object in
  let P := write_native P "Function" builtin_function in
  (* TODO: let P := write_native P "Array" builtin_array in 
  let P := write_native P "String" builtin_string in
  let P := write_native P "Boolean" builtin_boolean in
  let P := write_native P "Number" builtin_number in *)
  let P := write_native P "Math" builtin_math in
  let P := write_native P "Error" builtin_error in
  let P := write_native P "RangeError" builtin_range_error in
  let P := write_native P "ReferenceError" builtin_ref_error in
  let P := write_native P "SyntaxError" builtin_syntax_error in
  let P := write_native P "TypeError" builtin_type_error in
  P.  

(** Definition of the global object *)

Definition object_builtin_global :=
  object_create_builtin 
    object_builtin_global_proto 
    object_builtin_global_class
    object_builtin_global_properties.


(**************************************************************)
(** Object prototype object *)

(** Definition of the Object prototype object *)

Definition object_builtin_object_proto :=
  let P := Heap.empty in
  let P := write_constant P "constructor" builtin_object_new in
  let P := write_native P "isPrototypeOf" builtin_object_proto_is_prototype_of in
  (* TODO: complete list *)
  object_create_builtin null "Object" P.
    

(**************************************************************)
(** Object object *)

(** Definition of the Object object *)

Definition object_builtin_object :=
  let P := Heap.empty in
  let P := write_constant P "prototype" builtin_object_proto in
  let P := write_native P "get_prototype_of" builtin_object_get_prototype_of in
  (* TODO: complete list *)
  object_create_builtin_constructor builtin_object_call builtin_object_new 1 P.


(**************************************************************)
(** Function object *)

(**************************************************************)
(** Function prototype object *)

(**************************************************************)
(** Number object *)

(**************************************************************)
(** Number prototype object *)

(**************************************************************)
(** Array object *)

(**************************************************************)
(** Array prototype object *)

(**************************************************************)
(** String object *)

(**************************************************************)
(** String prototype object *)

(**************************************************************)
(** Bool object *)

(**************************************************************)
(** Bool prototype object *)

(**************************************************************)
(** Math object *)


(**************************************************************)
(** Initial object heap *)

Definition object_heap_initial :=
  let h : Heap.heap object_loc object := Heap.empty in
  let h := Heap.write h builtin_global object_builtin_global in
  let h := Heap.write h builtin_object object_builtin_object in
  let h := Heap.write h builtin_object_proto object_builtin_object_proto in
  (* TODO: update and uncomment once definitions have been completed
  let h := Heap.write h builtin_array_proto object_builtin_array_proto in
  let h := Heap.write h builtin_number_proto object_builtin_number_proto in
  let h := Heap.write h builtin_string_proto object_builtin_string_proto in
  let h := Heap.write h builtin_eval_proto object_builtin_eval_proto in
  let h := Heap.write h builtin_range_error object_builtin_range_error in
  let h := Heap.write h builtin_ref_error object_builtin_ref_error in
  let h := Heap.write h builtin_syntax_error object_builtin_syntax_error in
  let h := Heap.write h builtin_type_error object_builtin_type_error in
  ...etc
  *)
  h.  


(**************************************************************)
(** Initial environment record heap *)

Definition env_record_heap_initial :=
  Heap.write Heap.empty 
             env_loc_global_env_record
             (env_record_object_default builtin_global).


(**************************************************************)
(** TODO: remove this once Heap representation is fixed *)

CoFixpoint all_locations (k:nat) : stream nat := 
  stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 0%nat.


(**************************************************************)
(** Initial state *)

Definition state_initial := 
  {| state_object_heap := object_heap_initial; 
     state_env_record_heap := env_record_heap_initial;
     state_fresh_locations := dummy_fresh_locations |}.


(**************************************************************)
(** Initial lexical environment *)

(** Definition of the initial lexical context *)

Definition lexical_env_initial : lexical_env :=
  (env_loc_global_env_record)::nil.
