Set Implicit Arguments.
Require Export JsPreliminary JsPreliminaryAux.

(* TODO: (re)move *)

Coercion JsNumber.of_int : Z >-> JsNumber.number.

(**************************************************************)
(** ** Implicit Types -- copied from JsPreliminary *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
(*Implicit Type B : builtin.*)
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
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
    that is writable, non enumerable and configurable . *)

Definition prop_attributes_for_global_object v :=
   attributes_data_intro v true false true.

(** Shorthand notation for building a property attributes
    that is non writable, non configurable and non enumerable. *)

Definition attrib_constant v := 
  attributes_data_intro v false false false.

(** Shorthand notation for building a property attributes
    that is non writable, non configurable and non enumerable. *)

Notation "'attrib_native'" := prop_attributes_for_global_object.

(* TODO: might not need the above two notations *)

(** Builds an object with all optional fields to None
    and with extensible set to true *)

Definition object_create_builtin vproto sclass P :=
  object_create vproto sclass true P.

(** Builds a native object, with [prealloc_function_proto]
    as prototype, and a length property. *)

Definition object_create_prealloc_call_or_construct length P :=
  let sclass := "Function" in
  let P' := Heap.write P "length" (attrib_constant length) in
  (* The spec does not say anything special about [[get]] for built-in objects *)
  object_create_builtin prealloc_function_proto sclass P'.

(** Builds a native function object, like in the above function
    but with only a Call method implemented by builtin code. *)

Definition object_create_prealloc_call fprealloc length P :=
  let O := object_create_prealloc_call_or_construct length P in
  object_with_invokation O None (Some (call_prealloc fprealloc)) None.

(** Builds a native constructor object, with a Call method and
    a Construct method implemented by builtin code. *)

Definition object_create_prealloc_constructor fprealloc length P :=
  let O := object_create_prealloc_call_or_construct length P in
  object_with_invokation O (Some (construct_prealloc fprealloc)) (Some (call_prealloc fprealloc)) None.

(** Shorthand to extend a heap with a native method *)

Definition write_native P name v :=
  Heap.write P name (attrib_native v).

(** Shorthand to extend a heap with a constant *)

Definition write_constant P name value :=
  Heap.write P name (attrib_constant value).


(**************************************************************)
(** Global object *)

(** Implementation-dependent values for prototype and class fields
    of the global object *)

Parameter object_prealloc_global_proto : value.
Parameter object_prealloc_global_class : string.

(** Properties of the global object *)

Definition object_prealloc_global_properties :=
  let P := Heap.empty in
  let P := write_constant P "NaN" JsNumber.nan in
  let P := write_constant P "Infinity" JsNumber.infinity in
  let P := write_constant P "undefined" undef in
  let P := write_native P "eval" prealloc_global_eval in
  let P := write_native P "isNaN" prealloc_global_is_nan in
  let P := write_native P "isFinite" prealloc_global_is_finite in
  (* LATER: other functions to insert here *)
  let P := write_native P "Object" prealloc_object in
  let P := write_native P "Function" prealloc_function in
  (* LATER: let P := write_native P "Array" prealloc_array in
  let P := write_native P "String" prealloc_string in
  let P := write_native P "Boolean" prealloc_boolean in
  let P := write_native P "Number" prealloc_number in *)
  let P := write_native P "Math" prealloc_math in
  let P := write_native P "Error" prealloc_error in
  let P := write_native P "EvalError" native_error_eval in
  let P := write_native P "RangeError" native_error_range in
  let P := write_native P "ReferenceError" native_error_ref in
  let P := write_native P "SyntaxError" native_error_syntax in
  let P := write_native P "TypeError" native_error_type in
  P.


(** Definition of the global object *)

Definition object_prealloc_global :=
  object_create_builtin
    object_prealloc_global_proto
    object_prealloc_global_class
    object_prealloc_global_properties.
    
Definition global_eval_function_object :=
  object_create_prealloc_call prealloc_global_eval 1 Heap.empty.

Definition global_is_nan_function_object := 
  object_create_prealloc_call prealloc_global_is_nan 1 Heap.empty.
  
Definition global_is_finite_function_object :=
  object_create_prealloc_call prealloc_global_is_finite 1 Heap.empty.


(**************************************************************)
(** Object object *)

(** Definition of the Object object *)

Definition object_prealloc_object :=
  let P := Heap.empty in
  let P := write_constant P "prototype" prealloc_object_proto in
  let P := write_native P "getPrototypeOf" prealloc_object_get_proto_of in
  let P := write_native P "getOwnPropertyDescriptor" prealloc_object_get_own_prop_descriptor in
  let P := write_native P "getOwnPropertyNames" prealloc_object_get_own_prop_name in
  let P := write_native P "create" prealloc_object_create in
  let P := write_native P "defineProperty" prealloc_object_define_prop in
  let P := write_native P "defineProperties" prealloc_object_define_properties in
  let P := write_native P "seal" prealloc_object_seal in
  let P := write_native P "freeze" prealloc_object_freeze in
  let P := write_native P "preventExtensions" prealloc_object_prevent_extensions in
  let P := write_native P "isSealed" prealloc_object_is_sealed in
  let P := write_native P "isFrozen" prealloc_object_is_frozen in
  let P := write_native P "isExtensible" prealloc_object_is_extensible in
  (* LATER: complete list *)
  object_create_prealloc_constructor prealloc_object 1 P.
  
Definition object_get_prototype_of_function_object :=
  object_create_prealloc_call prealloc_object_get_proto_of 1 Heap.empty.


(**************************************************************)
(** Object prototype object *)

(** Definition of the Object prototype object *)

Definition object_prealloc_object_proto :=
  let P := Heap.empty in
  let P := write_native P "constructor" prealloc_object in
  let P := write_native P "toString" prealloc_object_proto_to_string in 
  let P := write_native P "valueOf" prealloc_object_proto_value_of in 
  let P := write_native P "isPrototypeOf" prealloc_object_proto_is_prototype_of in 
  object_create_builtin null "Object" P.
  
Definition object_proto_to_string_function_object :=
  object_create_prealloc_call prealloc_object_proto_to_string 0 Heap.empty.
  
Definition object_proto_value_of_function_object :=
  object_create_prealloc_call prealloc_object_proto_value_of 0 Heap.empty.
  
Definition object_proto_is_prototype_of_function_object :=
  object_create_prealloc_call prealloc_object_proto_is_prototype_of 1 Heap.empty.


(**************************************************************)
(** Function object *)

Definition object_prealloc_function :=
  let P := Heap.empty in
  let P := write_constant P "prototype" (value_object prealloc_function_proto) in
  let P := write_native P "get_prototype_of" prealloc_object_get_proto_of in (* This one seems odd, isn't it? -- Martin *)
  (* LATER: complete list *)
  object_create_prealloc_constructor prealloc_function 1 P.


(**************************************************************)
(** Function prototype object *)

Definition object_prealloc_function_proto :=
  let P := Heap.empty in
  let P := write_native P "constructor" prealloc_function in
  let P := Heap.write P "length" (attrib_constant 0) in (* todo: can we use write_constant? *)
  (* let P := write_native P "toString" prealloc_function_proto_to_string in *) (* TODO *)
  (* LATER: complete list *)
  let O := object_create_builtin prealloc_object_proto "Function" P in
  object_with_invokation O None (Some (call_prealloc prealloc_function_proto)) None.


(**************************************************************)
(** Number object *)

(* Daniele: ? *)

Definition object_prealloc_number :=
  let P := Heap.empty in
  (* TODO: what does this mean? --:: Daniele: use [prealloc_function_proto] when available *)
  (* Daiva: The spec says that Number.prototype is Number prototype object defined in 15.7.4 -- not a function prototype
            object. *)
  let P := write_constant P "prototype" prealloc_number_proto in
  let P := write_constant P "NaN" JsNumber.nan in
  let P := write_constant P "NEGATIVE_INFINITY" JsNumber.neg_infinity in
  let P := write_constant P "POSITIVE_INFINITY" JsNumber.infinity in
  (* TODO: complete list *)
  object_create_prealloc_constructor prealloc_number 1 P.


(**************************************************************)
(** Number prototype object *)

Definition object_prealloc_number_proto :=
  let P := Heap.empty in
  let P := write_native P "constructor" prealloc_number in
  let P := write_native P "toString" prealloc_number_proto_to_string in   
  let P := write_native P "valueOf" prealloc_number_proto_value_of in
  (* TODO: complete list *)
  let O := object_create_builtin prealloc_object_proto "Number" P in
  object_with_primitive_value O JsNumber.zero.
  
Definition number_proto_to_string_function_object :=
  object_create_prealloc_call prealloc_number_proto_to_string 0 Heap.empty.
  
Definition number_proto_value_of_function_object :=
  object_create_prealloc_call prealloc_number_proto_value_of 0 Heap.empty.


(**************************************************************)
(** Array object *)

(* LATER *)

(**************************************************************)
(** Array prototype object *)

(* LATER *)

(**************************************************************)
(** String object *)

(* LATER *)

(**************************************************************)
(** String prototype object *)

(* LATER *)

(**************************************************************)
(** Bool object *)

Definition object_prealloc_bool :=
  let P := Heap.empty in
  let P := write_native P "prototype" prealloc_bool_proto in
  (* TODO: complete list *)
  object_create_prealloc_constructor prealloc_bool 1 P.


(**************************************************************)
(** Bool prototype object *)

Definition object_prealloc_bool_proto :=
  let P := Heap.empty in
  let P := write_native P "constructor" prealloc_bool in
  let P := write_native P "toString" prealloc_bool_proto_to_string in   
  let P := write_native P "valueOf" prealloc_bool_proto_value_of in
  (* TODO: complete list *)
  let O := object_create_builtin prealloc_object_proto "Boolean" P in
  (* The spec does not say explicitly that [[PrimitiveValue]] is false. It says that object's value is false (15.6.4). TODO: do we need to change anything?*)
  object_with_primitive_value O false.
  
Definition bool_proto_to_string_function_object :=
  object_create_prealloc_call prealloc_bool_proto_to_string 0 Heap.empty. 
  
Definition bool_proto_value_of_function_object :=
  object_create_prealloc_call prealloc_bool_proto_value_of 0 Heap.empty. 


(**************************************************************)
(** Math object *)

(* TODO *)


(**************************************************************)
(** Error prototype object *)

(* TODO: the way we handle the property "constructor" everywhere in the file is boggous *)

Definition object_prealloc_error_proto :=
  let P := Heap.empty in
  let P := write_native P "constructor" prealloc_error in
  let P := write_native P "name" (prim_string "Error") in   
  let P := write_native P "message" (prim_string "") in   
  let P := write_native P "toString" prealloc_error_proto_to_string in   
  (* TODO: the spec does not talk about valueOf, is it intended? *)
  object_create_builtin prealloc_object_proto "Error" P.

Definition error_proto_to_string_function_object :=
  object_create_prealloc_call prealloc_error_proto_to_string 0 Heap.empty. 


(**************************************************************)
(** Error object *)

Definition object_prealloc_error :=
  let P := Heap.empty in
  let P := write_native P "prototype" prealloc_error_proto in
  object_create_prealloc_constructor prealloc_error 1 P.


(**************************************************************)
(** Native error prototype object *)

Definition object_prealloc_native_error_proto ne :=
  let P := Heap.empty in
  let P := write_native P "constructor" (prealloc_native_error ne) in
  let P := write_native P "name" (string_of_native_error ne) in   
  let P := write_native P "message" (prim_string "") in   
  object_create_builtin prealloc_error_proto "Error" P. 


(**************************************************************)
(** Native error object *)

Definition object_prealloc_native_error ne :=
  let P := Heap.empty in
  let P := write_native P "prototype" (prealloc_native_error_proto ne) in
  object_create_prealloc_constructor (prealloc_native_error_proto ne) 1 P.


(**************************************************************)
(** The [[ThrowTypeError]] Function Object  (13.2.3) *)

Definition throw_type_error_object :=  (* TODO: check this *)
  let o := object_create_prealloc_call prealloc_throw_type_error 0 Heap.empty in
  let o := object_with_scope o (Some lexical_env_initial) in
  let o := object_with_formal_params o (Some nil) in
  let o := object_set_extensible o false in
  o.


(**************************************************************)
(** Initial object heap *)

Definition object_heap_initial_function_objects (h : Heap.heap object_loc object) :=
  (* ThrowTypeError Function object *)
  let h := Heap.write h prealloc_throw_type_error throw_type_error_object in

  (* Function objects of Global object *)
  let h := Heap.write h prealloc_global_eval global_eval_function_object in
  let h := Heap.write h prealloc_global_is_nan global_is_nan_function_object in
  let h := Heap.write h prealloc_global_is_finite global_is_finite_function_object in
  
  (* Function objects of Object *)
  let h := Heap.write h prealloc_object_get_proto_of object_get_prototype_of_function_object in
  
  (* Function objects of Object.prototype *)
  let h := Heap.write h prealloc_object_proto_to_string object_proto_to_string_function_object in
  let h := Heap.write h prealloc_object_proto_value_of object_proto_value_of_function_object in
  let h := Heap.write h prealloc_object_proto_is_prototype_of object_proto_is_prototype_of_function_object in
  
  (* Function objects of Boolean.prototype *)
  let h := Heap.write h prealloc_bool_proto_to_string bool_proto_to_string_function_object in
  let h := Heap.write h prealloc_bool_proto_value_of bool_proto_value_of_function_object in
  
  (* Function objects of Number.prototype *)
  let h := Heap.write h prealloc_number_proto_to_string number_proto_to_string_function_object in
  let h := Heap.write h prealloc_number_proto_value_of number_proto_value_of_function_object in 

  (* Function objects of Error.prototype *)
  let h := Heap.write h prealloc_error_proto_to_string error_proto_to_string_function_object in

  h.

Definition object_heap_initial :=
  let h : Heap.heap object_loc object := Heap.empty in
  let h := Heap.write h prealloc_global object_prealloc_global in
  let h := Heap.write h prealloc_object object_prealloc_object in
  let h := Heap.write h prealloc_object_proto object_prealloc_object_proto in
  let h := Heap.write h prealloc_bool object_prealloc_bool in
  let h := Heap.write h prealloc_bool_proto object_prealloc_bool_proto in
  let h := Heap.write h prealloc_number object_prealloc_number in
  let h := Heap.write h prealloc_number_proto object_prealloc_number_proto in
  let h := Heap.write h prealloc_function object_prealloc_function in
  let h := Heap.write h prealloc_function_proto object_prealloc_function_proto in
  (* LATER : update and uncomment once definitions have been completed
  let h := Heap.write h prealloc_array_proto object_prealloc_array_proto in
  let h := Heap.write h prealloc_string_proto object_prealloc_string_proto in
  let h := Heap.write h prealloc_eval_proto object_prealloc_eval_proto in
  *)
  let h := Heap.write h prealloc_error_proto object_prealloc_error_proto in
  let h := Heap.write h (prealloc_native_error_proto native_error_eval) (object_prealloc_native_error_proto native_error_eval) in
  let h := Heap.write h (prealloc_native_error_proto native_error_range) (object_prealloc_native_error_proto native_error_range) in
  let h := Heap.write h (prealloc_native_error_proto native_error_ref) (object_prealloc_native_error_proto native_error_ref) in
  let h := Heap.write h (prealloc_native_error_proto native_error_syntax) (object_prealloc_native_error_proto native_error_syntax) in
  let h := Heap.write h (prealloc_native_error_proto native_error_type) (object_prealloc_native_error_proto native_error_type) in
  let h := Heap.write h prealloc_error object_prealloc_error in
  let h := Heap.write h native_error_eval (object_prealloc_native_error native_error_eval) in
  let h := Heap.write h native_error_range (object_prealloc_native_error native_error_range) in
  let h := Heap.write h native_error_ref (object_prealloc_native_error native_error_ref) in
  let h := Heap.write h native_error_syntax (object_prealloc_native_error native_error_syntax) in
  let h := Heap.write h native_error_type (object_prealloc_native_error native_error_type) in
  object_heap_initial_function_objects h.


(**************************************************************)
(** Initial environment record heap *)

Definition env_record_heap_initial :=
  Heap.write Heap.empty
             env_loc_global_env_record
             (env_record_object_default prealloc_global).


(**************************************************************)
(** TODO: remove this once Heap representation is fixed *)

CoFixpoint all_locations (k:nat) : stream nat :=
  stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat. (* Starting at 1 and not 0 because location 0 is already reserved for env_loc_global_env_record. *)


(**************************************************************)
(** Initial state *)

Definition state_initial :=
  {| state_object_heap := object_heap_initial;
     state_env_record_heap := env_record_heap_initial;
     state_fresh_locations := dummy_fresh_locations |}.

