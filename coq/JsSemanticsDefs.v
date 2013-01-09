Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux.

(**************************************************************)
(** ** Implicit Types *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type s : string.
Implicit Type i : literal.
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
Implicit Type E : env_record. (* suggested R *)
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
(** ** Operations on objects *)

(** Update the state by updating the object heap *)

Definition state_with_object_heap S new_object_heap :=
   match S with 
   | state_intro old_object_heap env_heap fresh_locs => 
     state_intro new_object_heap env_heap fresh_locs
   end.

(** Map a function to update the object heap of a state *)

Definition state_map_object_heap S F := 
  state_with_object_heap S (F (state_object_heap S)).

(** [object_write S l O] returns an updated state in which
    the location [l] is bound to the object [O]. *)

Definition object_write S l O :=
  state_map_object_heap S (fun H => Heap.write H l O).
  
(** [object_alloc S O] returns a pair [(L,S')]
    made of a fresh object location [L],
    and an updated state [S'] in which [L] is bound
    to the object [O]. *) 

Definition object_alloc S O :=
   match S with state_intro cells bindings (n:::alloc) =>
     let L := object_loc_normal n in
     (L, object_write S L O)
   end.

(** [object_binds S l O] asserts that [l] is bound to the object [O]
    in the heap of the state [S]. *)

Definition object_binds S l O :=
  Heap.binds (state_object_heap S) l O.

(** [object_indom S l] asserts that [l] is bound to some object
    in [S]. *)

 Definition object_indom S l :=
  Heap.indom (state_object_heap S) l.

(** [object_proto S l v] asserts that the prototype field 
    of the object stored at address [l] in [S] contains the 
    value [v]. *)

Definition object_proto S l v :=
  exists O, object_binds S l O /\ object_proto_ O = v.

(** [object_class S l s] asserts that the class field 
    of the object stored at address [l] in [S] contains the 
    value [s]. *)

Definition object_class S l s :=
  exists O, object_binds S l O /\ object_class_ O = s.

(** [object_extensible S l v] asserts that the extensible field 
    of the object stored at address [l] in [S] contains the 
    value [b]. *)

Definition object_extensible S l b :=
  exists O, object_binds S l O /\ object_extensible_ O = b.

(** [object_prim_value S l v] asserts that the primitive value
    field of the object stored at address [l] in [S] contains the 
    value [v]. *)

Definition object_prim_value S l v :=
  exists O, object_binds S l O /\ object_prim_value_ O = Some v.

(** [object_call S l fco] asserts that the primitive value
    field of the object stored at address [l] in [S] contains  
    an option [fco] which may contain function code. *)

Definition object_call S l fco :=
  exists O, object_binds S l O /\ object_call_ O = fco.

(** [object_formal_parameters S l fp] asserts that the [[FormalParameters]]
    field of the object stored at address [l] in [S] contains  
    an option [fp] which may contain function formal parameters. *)

Definition object_formal_parameters S l fp :=
  exists O, object_binds S l O /\ object_formal_parameters_ O = fp.

(** [object_properties S l P] asserts that [P]
    is the content of the properties field of the object 
    stored at address [l] in [S]. *)

Definition object_properties S l P :=
  exists O, object_binds S l O /\ P = object_properties_ O.

(** Map a function [F] on the properties field of an object,
    and returns the updated object. *)

Definition object_map_properties O F :=
  object_with_properties O (F (object_properties_ O)).

(* LATER: fix naming conventions to avoid the need to insert
   "heap" in the two functions below *)

(** [object_heap_set_properties S l P' S'] asserts that the state
    [S] contains an object at location [l], and that [S'] 
    describes the heap after updated the properties of the
    object at location [l] with the map [P']. *)

Definition object_heap_set_properties S l P' S' :=
  exists O, object_binds S l O 
         /\ S' = object_write S l (object_with_properties O P').

(** [object_heap_map_properties S l F S'] asserts that the state
    [S] contains an object at location [l], and that [S'] 
    describes the heap after updated the properties of the
    object at location [l] by mapping function [F] onto it. *)

Definition object_heap_map_properties S l F S' :=
  exists O, object_binds S l O 
         /\ S' = object_write S l (object_map_properties O F).

(** [object_has_property S l x] asserts that the object stored 
    at address [l] in [S] has a properties field that binds the
    property name [x]. *)

Definition object_has_property S l x :=
  exists O, object_binds S l O /\ Heap.indom (object_properties_ O) x.

(** [object_binds_property S l x P] asserts that the object stored 
    at address [l] in [S] has a properties field that binds the
    property name [x] to the attributes [A]. *)

Definition object_binds_property S l x A :=
  exists O, object_binds S l O /\ Heap.binds (object_properties_ O) x A.

(** [object_set_property S l x A] modifies the object stored 
    at address [l] in [S] to add or update a property named [x] 
    and binds it to the attributes [A]; The operation returns 
    the updated state. *)

Definition object_set_property S l x A :=
  object_heap_map_properties S l (fun P => Heap.write P x A).

(** [object_rem_property S l x A] removes from the object stored 
    at address [l] in [S] the property named [x]; The operation  
    returns the updated state. *)

Definition object_rem_property S l x S' :=
  object_heap_map_properties S l (fun P => Heap.rem P x) S'.


(**************************************************************)
(** ** Smart constructors for property descriptors *)

(** Constructs a property descriptor with only the value field set *)

Definition prop_attributes_create_value v := {|
   prop_attributes_value := Some v;
   prop_attributes_writable := None;
   prop_attributes_get := None;
   prop_attributes_set := None;
   prop_attributes_enumerable := None;
   prop_attributes_configurable := None |}.

(** Constructs a fully-populated data property descriptor *)

Definition prop_attributes_create_data v bw be bc := {|
   prop_attributes_value := Some v;
   prop_attributes_writable := Some bw;
   prop_attributes_get := None;
   prop_attributes_set := None;
   prop_attributes_enumerable := Some be;
   prop_attributes_configurable := Some bc |}.

(** Constructs a fully-populated data property descriptor
    for a constant value *)

Definition prop_attributes_create_data_constant v :=
   prop_attributes_create_data v false false false.

(** Constructs a fully-populated data property descriptor
    for a writable value *)

Definition prop_attributes_create_data_writable v :=
   prop_attributes_create_data v true false false.

(** Constructs a fully-populated data property descriptor
    for a writable and configurable value *)

Definition prop_attributes_create_data_configurable v :=
   prop_attributes_create_data v true false true.

(** Constructs a fully-populated accessor property descriptor *)

Definition prop_attributes_create_accessor vset vget be bc := {|
   prop_attributes_value := None;
   prop_attributes_writable := None;
   prop_attributes_get := Some vget;
   prop_attributes_set := Some vset;
   prop_attributes_enumerable := Some be;
   prop_attributes_configurable := Some bc |}.

(** Two auxiliary functions for the subsequently-defined functions *)

Definition prop_attributes_field_or_false F A :=
  match F A with
  | None => false
  | Some b => b
  end.
  
Definition prop_attributes_field_or_undef F A :=
  match F A with
  | None => undef
  | Some b => b
  end.

(** Converts a property descriptor into a data descriptor *)

Definition prop_attributes_convert_to_data A := {|
   prop_attributes_value := Some (prop_attributes_field_or_undef prop_attributes_value A);
   prop_attributes_writable := Some (prop_attributes_field_or_false prop_attributes_writable A);
   prop_attributes_get := None;
   prop_attributes_set := None;
   prop_attributes_enumerable := Some (prop_attributes_field_or_false prop_attributes_enumerable A);
   prop_attributes_configurable := Some (prop_attributes_field_or_false prop_attributes_configurable A) |}.

(** Converts a property descriptor into an accessor descriptor *)

Definition prop_attributes_convert_to_accessor A := {|
   prop_attributes_value := None;
   prop_attributes_writable := None;
   prop_attributes_get := Some (prop_attributes_field_or_undef prop_attributes_get A);
   prop_attributes_set := Some (prop_attributes_field_or_undef prop_attributes_set A);
   prop_attributes_enumerable := Some (prop_attributes_field_or_false prop_attributes_enumerable A);
   prop_attributes_configurable := Some (prop_attributes_field_or_false prop_attributes_configurable A) |}.


(**************************************************************)
(** ** Classification of property descriptors *)

(** Characterization of data descriptors *)

Definition prop_attributes_is_data A :=
 ~ (   prop_attributes_value A = None 
    /\ prop_attributes_writable A = None).

(** Characterization of non-null data descriptors *)

Definition prop_descriptor_is_data An :=
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => prop_attributes_is_data A
  end.

(** Characterization of accessor descriptors *)

Definition prop_attributes_is_accessor A :=
 ~ (   prop_attributes_get A = None 
    /\ prop_attributes_set A = None).

(** Characterization of non-null accessor descriptors *)

Definition prop_descriptor_is_accessor An :=
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => prop_attributes_is_accessor A
  end.

(** Characterization of generic descriptors *)

Definition prop_attributes_is_generic A :=
     ~ prop_attributes_is_accessor A
  /\ ~ prop_attributes_is_data A.

(** Characterization of non-null generic descriptors *)

Definition prop_descriptor_is_generic An :=
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => prop_attributes_is_generic A
  end.

(** Characterization of fully-populated data descriptors *)

Definition prop_attributes_fully_populated_data A :=
     prop_attributes_value A <> None
  /\ prop_attributes_writable A <> None
  /\ prop_attributes_enumerable A <> None
  /\ prop_attributes_configurable A <> None.

(** Characterization of non-null fully-populated data descriptors *)

Definition prop_descriptor_fully_populated_data An :=
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => prop_attributes_fully_populated_data A
  end.

(** Characterization of fully-populated accessor descriptors *)

Definition prop_attributes_fully_populated_accessor A :=
     prop_attributes_get A <> None
  /\ prop_attributes_set A <> None
  /\ prop_attributes_enumerable A <> None
  /\ prop_attributes_configurable A <> None.

(** Characterization of non-null fully-populated accessor descriptors *)

Definition prop_descriptor_fully_populated_accessor An :=
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => prop_attributes_fully_populated_accessor A
  end.

(** Characterization of fully-populated descriptors *)

Definition prop_attributes_fully_populated An :=
    (prop_descriptor_is_data An /\ prop_descriptor_fully_populated_data An)
 \/ (prop_descriptor_is_accessor An /\ prop_descriptor_fully_populated_accessor An).

 (* TEMP: alternative definition:
  match An with
  | prop_descriptor_undef => False
  | prop_descriptor_some A => 
         (   prop_attributes_is_data A 
         /\ prop_attributes_fully_populated_accessor A)
     \/ (prop_attributes_is_accessor A  
         /\ prop_attributes_fully_populated_accessor A).
  end.
  *)


(**************************************************************)
(** ** Auxiliary functions on references *)

(** The helper function [ref_kind_of] returns values given
    by the grammar [ref_kind]. This helper functions serves 
    as a basis for implementing methods characterizing the 
    different kind of references. *)

Inductive ref_kind := 
  | ref_kind_null
  | ref_kind_undef
  | ref_kind_primitive_base
  | ref_kind_object
  | ref_kind_env_record.

Definition ref_kind_of r :=
  match ref_base r with
  | ref_base_type_value v =>
    match v with
    | value_prim w =>
       match w with
       | prim_undef => ref_kind_undef
       | prim_null => ref_kind_null
       | prim_bool _ => ref_kind_primitive_base
       | prim_number _ => ref_kind_primitive_base
       | prim_string _ => ref_kind_primitive_base
       end
    | value_object _ => ref_kind_object
    end
 | ref_base_type_env_loc L =>
     ref_kind_env_record
 end.

(** [ref_has_primitive_base r] asserts that the reference [r]
    has a base value which is a boolean, a number or a string. *)

Definition ref_has_primitive_base r :=
  ref_kind_of r = ref_kind_primitive_base.

(** [ref_is_property r] asserts that the reference [r]
    either has a primitive base or has an object as base. *)

Definition ref_is_property r :=
  let k := ref_kind_of r in
     k = ref_kind_primitive_base
  \/ k = ref_kind_object.

(** [ref_is_unresolvable r] asserts that the reference [r]
    as either [undef] for base. *)

Definition ref_is_unresolvable r :=
  ref_kind_of r = ref_kind_undef.  (* todo: double check *)
  
(** [ref_create_value] is a smart constructor for building 
    a reference on top of a value. *)

Definition ref_create_value v x strict :=
  {| ref_base := ref_base_type_value v;
     ref_name := x;
     ref_strict := strict |}.

(** [ref_create_env_loc] is a smart constructor for building 
    a reference on top of the location of an environment record. *)

Definition ref_create_env_loc L x strict :=
  {| ref_base := ref_base_type_env_loc L;
     ref_name := x;
     ref_strict := strict |}.


(**************************************************************)
(** ** Operations on mutability flags *)

(** Smart constructor for building a mutability flag from a boolean *)

Definition mutability_of_bool deletable :=
  if (deletable:bool)
    then mutability_deletable 
    else mutability_nondeletable. 

(** Characterization of mutability flags that allow for a mutation *)

Definition mutability_is_mutable mu :=
  mu <> mutability_immutable. 


(**************************************************************)
(** ** Operations on environment records *)

(** Update the state by updating the environment record heap *)

Definition state_with_env_record_heap S new_env_heap :=
   match S with 
   | state_intro object_heap old_env_heap fresh_locs => 
     state_intro object_heap new_env_heap fresh_locs
   end.

(** Map a function to update the environment record heap of a state *)

Definition state_map_env_record_heap S F := 
  state_with_env_record_heap S (F (state_env_record_heap S)).

(** [env_record_write S L E] modifies the state [S] in order
    to write the object record [E] at location [L].
    The operation returns the updated state. *)

Definition env_record_write S L E :=
   state_map_env_record_heap S (fun H => Heap.write H L E).

(** [env_record_alloc S E] returns a pair [(L,S')]
    made of a fresh environment record location [L],
    and an updated state [S'] in which [L] is bound
    to the environment record [E]. *) 

Definition env_record_alloc S E :=
   (* TODO: implem will change; it should use env_record_write. *)
   match S with state_intro cells bindings (L:::alloc) =>
     let bindings' := Heap.write bindings L E in
     (L, state_intro cells bindings' alloc)
   end.

(** [env_record_binds S L E] asserts that [L] is bound to 
    the environment record [E] in the state [S]. *)

Definition env_record_binds S L E :=
  Heap.binds (state_env_record_heap S) L E.

(** Shorthand for provide_this falgs. *)

Definition provide_this_true : provide_this_flag := true.
Definition provide_this_false : provide_this_flag := false.

(** A smart constructor for building an object environment 
    record on an object [l], using the value [false] for the
    [provide_this] field. (This is the default behavior.) *)

Definition env_record_object_default l :=
  env_record_object l provide_this_false.


(**************************************************************)
(** ** Operations on declarative environments *)

(** The empty declarative environment *)

Definition decl_env_record_empty : decl_env_record :=
  Heap.empty.

(** [decl_env_record_binds D x mu v] asserts that the
    declarative environment [D] maps the property name
    [x] to the value [v] with the mutability flag [mu] *)

Definition decl_env_record_binds D x (mu : mutability) v :=
  Heap.binds D x (mu, v).

(** [decl_env_record_indom D x] asserts that the
    declarative environment [D] binds the property name [x]. *)

Definition decl_env_record_indom D x := 
  Heap.indom (D:decl_env_record) x. 

(** [decl_env_record_write D x mu v] returns an updated
    declarative enviromnent with a new binding from [x] to
    [v] with mutability flag [mu]. *)

Definition decl_env_record_write D x mu v : decl_env_record :=
  Heap.write D x (mu, v).

(** [decl_env_record_rem D x] returns an updated declarative 
    enviromnent with a new binding for [x] removed. *)

Definition decl_env_record_rem D x : decl_env_record :=
  Heap.rem (D:decl_env_record) x.

(** TODO: Change the following definition to a relation. *)

Definition env_record_write_decl_env S L x mu v := 
  match Heap.read (state_env_record_heap S) L with
  | env_record_decl D => 
     let env' := decl_env_record_write D x mu v in
     env_record_write S L (env_record_decl env')
  | env_record_object _ _ => S (* It should never happen *)
  end. 


(**************************************************************)
(** ** Operations on lexical environment *)

(** [lexical_env_alloc S lex E] returns a pair [(lex',S')]
    made of lexical environment [le'] that extends the
    lexical environment [lex] with a environment record
    location [L], which, in the updated state [S'],
    is bound to an environment record [E]. *) 

Definition lexical_env_alloc S lex E :=
  let '(L,S') := env_record_alloc S E in
  let lex' := (L::lex) in
  (lex',S').

(** [lexical_env_alloc_decl S lex] returns a pair [(lex',S')]
    made of lexical environment [lex'] that extends the
    lexical environment [lex] with an environment record
    bound at some location [L], which is bound in the 
    updated state [S'] to an empty declarative environment. *) 

Definition lexical_env_alloc_decl S lex :=
  lexical_env_alloc S lex decl_env_record_empty.

(** [lexical_env_alloc_object S lex l pt] returns a pair [(lex',S')]
    made of lexical environment [le'] that extends the
    lexical environment [lex] with an environment record
    at some location [L], which, in the updated state [S'],
    is bound to an object environment record built on the
    object location [l]. [pt] is used for [provide_this] flag. *) 

Definition lexical_env_alloc_object S lex l pt :=
  lexical_env_alloc S lex (env_record_object l pt).


(**************************************************************)
(** ** Operations on execution contexts *)

(** A smart constructor for execution contexts whose variable
    context is identical to their lexical context. *)

Definition execution_ctx_intro_same X lthis strict :=
  execution_ctx_intro X X lthis strict.

(** A smart constructor for modifying the lexical environment
    of an execution context. *)

Definition execution_ctx_with_lex C lex :=
  match C with execution_ctx_intro x1 x2 x3 x4 =>
    execution_ctx_intro lex x2 x3 x4 end.

(** A smart constructor for modifying an execution context 
    by changing the lexical environment and the this binding
    of an execution context. *)

Definition execution_ctx_with_lex_this C lex lthis :=
  match C with execution_ctx_intro x1 x2 x3 x4 =>
    execution_ctx_intro lex x2 lthis x4 end.
    
(**************************************************************)
(** ** Auxilary functions for function_code *)  

Definition function_code_strict fc :=
  match fc with
    | function_code_code p => function_body_is_strict p
    | function_code_builtin _ => false
  end. 
  
(* TODO : retrieve function and variable declarations from code *)
Parameter function_declarations : function_code -> list function_declaration.  
Parameter variable_declarations : function_code -> list string.


(****************************************************************)
(** ** Intermediate expression for the Pretty-Big-Step semantic *)

(** Grammar of preferred types for use by the default_value 
    conversion. *)

Inductive preftype :=
  | preftype_number
  | preftype_string.

Implicit Type pref : preftype. 

(** Grammar of extended expressions *)

Inductive ext_expr :=

  (** Extended expressions include expressions *)

  | expr_basic : expr -> ext_expr

  (** Extended expressions for lists of expressions *)

  | expr_list_then : (list value -> ext_expr) -> list expr -> ext_expr (* [expr_list_then k es] evaluates all the expressions of [es], then call [k] on the generated list of value. *)
  | expr_list_then_1 : (list value -> ext_expr) -> list value -> list expr -> ext_expr (* [expr_list_then_1 k vs es] has already computed all the values [vs], and starts executing [es]. *)
  | expr_list_then_2 : (list value -> ext_expr) -> list value -> out -> list expr -> ext_expr (* [expr_list_then_2 k vs o es] has evaluated the first of the expressions left, that has returned [o]. *)

  (** Extended expressions associated with primitive expressions *)

  | expr_object_1 : object_loc -> list string -> list value -> ext_expr (* All the expressions of the object have been evaluated. *)

  | expr_access_1 : out -> expr -> ext_expr (* The left expression has been executed *)
  | expr_access_2 : object_loc -> out -> ext_expr (* The left expression has been converted to a location and the right expression is executed. *)
  | expr_access_3 : value -> value -> ext_expr

  | expr_new_1 : out -> list expr -> ext_expr (* The function has been evaluated. *)
  | expr_new_2 : object_loc -> function_code -> list value -> ext_expr (* The arguments too. *)
  | expr_new_3 : object_loc -> out -> ext_expr (* The call has been executed. *)
  | expr_call_1 : out -> list expr -> ext_expr (* The function has been evaluated. *) 
  | expr_call_2 : object_loc -> object_loc -> list expr -> ext_expr (* A check is performed on the location returned to know if it's a special one. *)
  | expr_call_3 : object_loc -> function_code -> list value -> ext_expr (* The arguments have been executed. *)
  | expr_call_4 : out -> ext_expr (* The call has been executed. *)

  | expr_unary_op_1 : unary_op -> out -> ext_expr (* The argument have been executed. *)
  | expr_unary_op_2 : unary_op -> value -> ext_expr (* The argument is a value. *)
  | expr_binary_op_1 : out -> binary_op -> expr -> ext_expr (* The right argument have been executed. *)
  | expr_binary_op_2 : option out -> value -> binary_op -> expr -> ext_expr (* The execution checks if this value matches the lazy evaluation rules. *)
  | expr_binary_op_3 : value -> binary_op -> ext_expr -> ext_expr (* It does not:  the right expression is executed. *)
  | expr_binary_op_4 : value -> binary_op -> out -> ext_expr
  | expr_binary_op_5 : value -> binary_op -> value -> ext_expr
  | expr_binary_op_add_1 : value -> value -> ext_expr

  | expr_assign_1 : out -> option binary_op -> expr -> ext_expr (* The left expression has been executed *)
  | expr_assign_2 : ref -> out -> ext_expr (* The right expression has been executed *)
  | expr_assign_3 : ref -> value -> ext_expr
  | expr_assign_2_op : ref -> value -> binary_op -> out -> ext_expr (* The right expression has been executed and there was an operator.  *)

(* TODO: we could separate ext_spec from ext_expr,
   and separate red_spec from red_expr *)

  (** Extended expressions for conversions *)

  | spec_to_primitive : value -> preftype -> ext_expr 
  | spec_to_boolean : value -> ext_expr
  | spec_to_number : value -> ext_expr
  | spec_to_number_1 : out -> ext_expr
  | spec_to_integer : value -> ext_expr
  | spec_to_integer_1 : out -> ext_expr
  | spec_to_string : value -> ext_expr
  | spec_to_string_1 : out -> ext_expr
  | spec_to_object : value -> ext_expr
  | spec_check_object_coercible : value -> ext_expr

  | spec_to_default : object_loc -> preftype -> ext_expr 
  | spec_to_default_1 : object_loc -> preftype -> preftype -> ext_expr
  | spec_to_default_2 : object_loc -> preftype -> ext_expr
  | spec_to_default_3 : ext_expr
  | spec_to_default_sub_1 : object_loc -> string -> ext_expr -> ext_expr
  | spec_to_default_sub_2 : object_loc -> out -> expr -> ext_expr
  | spec_to_default_sub_3 : out -> ext_expr -> ext_expr
  | spec_to_default_sub_4 : value -> ext_expr -> ext_expr

  | spec_convert_twice : ext_expr -> ext_expr -> (value -> value -> ext_expr) -> ext_expr
  | spec_convert_twice_1 : out -> ext_expr -> (value -> value -> ext_expr) -> ext_expr
  | spec_convert_twice_2 : out -> (value -> ext_expr) -> ext_expr


  (** Extended expressions for conversions *)
  | spec_eq : value -> value -> ext_expr
  | spec_eq0 : value -> value -> ext_expr
  | spec_eq1 : value -> value -> ext_expr
  | spec_eq2 : ext_expr -> value -> value -> ext_expr

  (** Extended expressions for operations on objects *)

  | spec_object_get : value -> prop_name -> ext_expr 
  | spec_object_get_1 : object_loc -> prop_descriptor -> ext_expr 
  | spec_object_get_2 : object_loc -> option value -> ext_expr
  | spec_object_can_put : object_loc -> prop_name -> ext_expr
  | spec_object_can_put_1 : object_loc -> prop_name -> prop_descriptor -> ext_expr
  | spec_object_can_put_2 : object_loc -> prop_name -> bool -> ext_expr
  | spec_object_can_put_3 : object_loc -> prop_name -> value -> ext_expr
  | spec_object_can_put_4 : object_loc -> prop_descriptor -> ext_expr
  | spec_object_put : object_loc -> prop_name -> value -> bool -> ext_expr
  | spec_object_put_1 : object_loc -> prop_name -> value -> bool -> out -> ext_expr
  | spec_object_put_2 : object_loc -> prop_name -> value -> bool -> prop_descriptor -> ext_expr
  | spec_object_put_3 : object_loc -> prop_name -> value -> bool -> prop_descriptor -> ext_expr
  | spec_object_get_special : value -> prop_name -> ext_expr
  | spec_object_get_special_1 : prop_name -> out -> ext_expr
  | spec_object_put_special : value -> prop_name -> value -> bool -> ext_expr
  | spec_object_has_prop : object_loc -> prop_name -> ext_expr
  | spec_object_delete : object_loc -> prop_name -> bool -> ext_expr
  | spec_object_delete_1 : object_loc -> prop_name -> bool -> prop_descriptor -> ext_expr
  | spec_object_delete_2 : object_loc -> prop_name -> bool -> bool -> ext_expr
 
  | spec_object_define_own_prop : object_loc -> prop_name -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_1 : object_loc -> prop_name -> prop_descriptor -> prop_attributes -> bool -> bool -> ext_expr
  | spec_object_define_own_prop_2 : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_3 : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_4a : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_4b : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_4c : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr
  | spec_object_define_own_prop_5 : object_loc -> prop_name -> prop_attributes -> prop_attributes -> bool -> ext_expr

  (** Extended expressions for operations on references *)

  | spec_ref_get_value : ret -> ext_expr
  | spec_ref_put_value : ret -> value -> ext_expr

  (** Shorthand for calling [red_expr] then [ref_get_value] *)

  | spec_expr_get_value : expr -> ext_expr 
  | spec_expr_get_value_1 : out -> ext_expr

  (** Extended expressions for operations on environment records *)

  | spec_env_record_has_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_has_binding_1 : env_loc -> prop_name -> env_record -> ext_expr
  | spec_env_record_get_binding_value : env_loc -> prop_name -> bool -> ext_expr
  | spec_env_record_get_binding_value_1 : env_loc -> prop_name -> bool -> env_record -> ext_expr
  | spec_env_record_get_binding_value_2 : prop_name -> bool -> object_loc -> out -> ext_expr
  | spec_env_record_set_binding_value : env_loc -> prop_name -> value -> bool -> ext_expr

  | spec_env_record_create_immutable_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_initialize_immutable_binding : env_loc -> prop_name -> value -> ext_expr
  | spec_env_record_create_mutable_binding : env_loc -> prop_name -> option bool -> ext_expr
  | spec_env_record_create_mutable_binding_1 : env_loc -> prop_name -> bool -> env_record -> ext_expr
  | spec_env_record_create_mutable_binding_2 : env_loc -> prop_name -> bool -> object_loc -> out -> ext_expr
  | spec_env_record_set_mutable_binding : env_loc -> prop_name -> value -> bool -> ext_expr
  | spec_env_record_set_mutable_binding_1 : env_loc -> prop_name -> value -> bool -> env_record -> ext_expr
  | spec_env_record_delete_binding : env_loc -> prop_name -> ext_expr
  | spec_env_record_delete_binding_1 : env_loc -> prop_name -> env_record -> ext_expr

  | spec_env_record_create_set_mutable_binding : env_loc -> prop_name -> option bool -> value -> bool -> ext_expr
  | spec_env_record_create_set_mutable_binding_1 : out -> env_loc -> prop_name -> value -> bool -> ext_expr

  | spec_env_record_implicit_this_value : env_loc -> prop_name -> ext_expr
  | spec_env_record_implicit_this_value_1 : env_loc -> prop_name -> env_record -> ext_expr

  (** Extended expressions for operations on lexical environments *)

  | spec_lexical_env_get_identifier_ref : lexical_env -> prop_name -> bool -> ext_expr
  | spec_lexical_env_get_identifier_ref_1 : env_loc -> lexical_env -> prop_name -> bool -> ext_expr
  | spec_lexical_env_get_identifier_ref_2 : env_loc -> lexical_env -> prop_name -> bool -> out -> ext_expr

  (** Extended expressions for function calls *)

  (* TODO: the definitions below will change *)
  | spec_execution_ctx_function_call : type -> function_code -> value -> list value -> ext_expr
  | spec_execution_ctx_function_call_1 : type -> function_code -> list value -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation : type -> option object_loc -> function_code -> list value -> ext_expr
  | spec_execution_ctx_binding_instantiation_1 : type -> option object_loc -> function_code -> list value -> env_loc -> ext_expr
  | spec_execution_ctx_binding_instantiation_2 : type -> object_loc -> function_code -> list value -> env_loc -> list string -> ext_expr
  | spec_execution_ctx_binding_instantiation_3 : type -> object_loc -> function_code -> list value -> env_loc -> string -> list string -> value -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_4 : type -> object_loc -> function_code -> list value -> env_loc -> string -> list string -> value -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_5 : type -> object_loc -> function_code -> list value -> env_loc -> list string -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_6 : type -> option object_loc -> function_code -> list value -> env_loc -> ext_expr
  | spec_execution_ctx_binding_instantiation_7 : type -> option object_loc -> function_code -> list value -> env_loc -> list function_declaration -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_8 : type -> option object_loc -> function_code -> list value -> env_loc -> function_declaration -> list function_declaration -> strictness_flag -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_9 : type -> option object_loc -> function_code -> list value -> env_loc -> function_declaration -> list function_declaration -> strictness_flag -> object_loc -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_10 : type -> option object_loc -> function_code -> list value -> function_declaration -> list function_declaration -> strictness_flag -> object_loc -> prop_attributes -> option bool -> ext_expr
  | spec_execution_ctx_binding_instantiation_11 : type -> option object_loc -> function_code -> list value -> env_loc -> function_declaration -> list function_declaration -> strictness_flag -> object_loc -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_12 : type -> option object_loc -> function_code -> list value -> env_loc -> ext_expr
  | spec_execution_ctx_binding_instantiation_13 : type -> option object_loc -> function_code -> list value -> env_loc -> list string -> out -> ext_expr
  | spec_execution_ctx_binding_instantiation_14 : type -> option object_loc -> function_code -> list value -> env_loc -> string -> list string -> out -> ext_expr
  
  | spec_creating_function_object : list string -> function_code -> lexical_env -> strictness_flag -> ext_expr
  | spec_creating_function_object_1 : list string -> function_code -> lexical_env -> strictness_flag -> object -> out -> ext_expr

(** Grammar of extended statements *)

with ext_stat :=

  (** Extended expressions include statements *)

  | stat_basic : stat -> ext_stat

  (** Extended statements associated with primitive statements *)

  | stat_seq_1 : out -> stat -> ext_stat (* The first statement has been executed. *)
  
  | stat_var_decl_1 : out -> ext_stat (* Ignore its argument and returns [undef] *)

  | stat_if_1 : value -> stat -> option stat -> ext_stat

  (* TODO: arthur suggests changing the order of the arguments so that expr and stat are always the last two arguments *)
  | stat_while_1 : expr -> stat -> value -> ext_stat (* The condition have been executed. *)
  | stat_while_2 : expr -> stat -> out -> ext_stat (* The condition have been executed and converted to a boolean. *)
  
  | stat_for_in_1 : expr -> stat -> out -> ext_stat
  | stat_for_in_2 : expr -> stat -> out -> ext_stat
  | stat_for_in_3 : expr -> stat -> out -> ext_stat
  | stat_for_in_4 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> ext_stat
  | stat_for_in_5 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> prop_name -> ext_stat
  | stat_for_in_6 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> prop_name -> ext_stat
  | stat_for_in_7 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> out -> ext_stat
  | stat_for_in_8 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> out -> ext_stat
  | stat_for_in_9 : expr -> stat -> object_loc -> option ret -> option out -> set prop_name -> set prop_name -> res -> ext_stat

  | stat_with_1 : stat -> value -> ext_stat (* The expression have been executed. *)
  
  | stat_throw_1 : out -> ext_stat (* The expression have been executed. *)

  | stat_try_1 : out -> option (string*stat) -> option stat -> ext_stat (* The try block has been executed. *)
  | stat_try_2 : out -> lexical_env -> stat -> option stat -> ext_stat (* The catch block is actived and will be executed. *)
  | stat_try_3 : out -> option stat -> ext_stat (* The try catch block has been executed:  there only stay an optional finally. *)
  | stat_try_4 : res -> out -> ext_stat (* The finally has been executed. *)

  (* Auxiliary forms for performing [red_expr] then [ref_get_value] and a conversion *)

  | spec_expr_get_value_conv : expr -> (value -> ext_expr) -> (value -> ext_stat) -> ext_stat
  | spec_expr_get_value_conv_1 : out -> (value -> ext_expr) -> (value -> ext_stat) -> ext_stat
  | spec_expr_get_value_conv_2 : out -> (value -> ext_stat) -> ext_stat

(** Grammar of extended programs *)

with ext_prog :=

  (** Extended expressions include statements *)

  | prog_basic : prog -> ext_prog

  (** Extended programs associated with primitive programs *)

  | prog_seq_1 : out -> prog -> ext_prog (* The first program has been executed. *)
.


(** Coercions *)

Coercion expr_basic : expr >-> ext_expr.
Coercion stat_basic : stat >-> ext_stat.
Coercion prog_basic : prog >-> ext_prog.


(**************************************************************)
(** ** Extracting outcome from an extended expression. *)

(** The [out_of_ext_*] family of definitions is used by
    the generic abort rule, which propagates exceptions,
    and divergence, break and continues. *)

Definition out_of_ext_expr (e : ext_expr) : option out :=
  match e with
  (* TODO: update later
  | expr_basic _ => None
  | expr_list_then _ _ => None
  | expr_list_then_1 _ _ _ => None
  | expr_list_then_2 _ _ o _ => Some o
  | expr_object_1 _ _ _ => None
  | expr_access_1 o _ => Some o
  | expr_access_2 _ o => Some o
  | expr_new_1 o _ => Some o
  | expr_new_2 _ _ _ => None
  | expr_new_3 _ o => Some o
  | expr_call_1 o _ => Some o
  | expr_call_2 _ _ _ => None
  | expr_call_3 _ _ _ => None
  | expr_call_4 o => Some o
  | expr_unary_op_1 _ o => Some o
  | expr_unary_op_2 _ _ => None
  | expr_binary_op_1 o _ _ => Some o
  | expr_binary_op_2 _ _ _ _ => None
     (* TODO (Arthur does not understand this comment:
        If the `option out' is not `None' then the `out' is returned anyway, 
        independently of wheither it aborts or not. *)
  | expr_binary_op_3 _ _ _ => None
  | expr_binary_op_add_1 _ _ => None
  | expr_assign_1 o _ _ => Some o
  | expr_assign_2 _ o => Some o
  | expr_assign_2_op _ _ _ o => Some o
  | spec_to_number_1 o => Some o
  | spec_to_integer_1 o => Some o
  | spec_to_string_1 o => Some o
  | spec_to_default_1 _ _ _ => None
  | spec_to_default_2 _ _ => None
  | spec_to_default_3 => None
  | spec_to_default_sub_1 _ _ _ => None
  | spec_to_default_sub_2 _ _ _ => None
  | spec_convert_twice _ _ _ => None
  | spec_convert_twice_1 o _ _ => Some o
  | spec_convert_twice_2 o _ => Some o
  (* TODO: missing new extended forms here *)
  *)
  | _ => None 
  (* TODO: remove the line above to ensure that nothing forgotten *)
  end.

Definition out_of_ext_stat (p : ext_stat) : option out :=
  match p with
  (* TODO: update later
  | stat_basic _ => None
  | stat_seq_1 o _ => Some o
  | stat_var_decl_1 o => Some o
  | stat_if_1 o _ _ => Some o
  | stat_if_2 o _ _ => out_some_out o
  | stat_if_3 o _ _ => out_some_out o
  | stat_while_1 _ o _ => Some o
  | stat_while_2 _ _ _ => None
  | stat_while_3 _ _ o => Some o
  | stat_throw_1 o => Some o
  | stat_try_1 o _ _=> Some o
  | stat_try_2 _ _ _ => None
  | stat_try_3 o _ => Some o
  | stat_try_4 _ o => Some o
  | stat_with_1 o _ => Some o
  *)
  | _ => None
  end.

Definition out_of_ext_prog (p : ext_prog) : option out :=
  match p with
  | prog_basic _ => None
  | prog_seq_1 o _ => Some o
  end.


(**************************************************************)
(** ** Rules for propagating aborting expressions *)

(** Definition of aborting programs --
   TODO: define [abort] as "not a normal behavior",
   by taking the negation of being of the form [ter (normal ...)]. *)

Inductive abort : out -> Prop :=
  | abort_div :
      abort out_div
  | abort_break : forall S la,
      abort (out_ter S (res_break la))
  | abort_continue : forall S la,
      abort (out_ter S (res_continue la))
  | abort_return : forall S la,
      abort (out_ter S (res_return la))
  | abort_throw : forall S v,
      abort (out_ter S (res_throw v)).

(** Definition of normal results -- TODO: not used ? *)

Inductive is_res_normal : res -> Prop :=
  | is_res_normal_intro : forall v,
      is_res_normal (res_normal v).

(** Definition of exception results, used in the
    semantics of try-catch blocks. *)

Inductive is_res_throw : res -> Prop :=
  | is_res_throw_intro : forall v,
      is_res_throw (res_throw v).
      
Inductive is_res_break : res -> Prop :=
  | is_res_break_intro : forall label,
      is_res_break (res_break label).

Inductive is_res_continue : res -> Prop :=
  | is_res_continue_intro: forall label,
      is_res_continue (res_continue label).

(** Definition of the behaviors caught by an exception handler,
    and thus not propagated by the generic abort rule *)

Inductive abort_intercepted : ext_stat -> out -> Prop :=
  | abort_intercepted_stat_try_1 : forall S v cb fio o,
      abort_intercepted (stat_try_1 o (Some cb) fio) (out_ter S (res_throw v))
  | abort_intercepted_stat_try_3 : forall S r fio o,
      abort_intercepted (stat_try_3 o fio) (out_ter S r).


(**************************************************************)
(** Macros for exceptional behaviors in reduction rules *)

(** "Syntax error" behavior *)

Definition out_basic_error S :=
  out_ter S (res_throw builtin_syntax_error).

(** "Type error" behavior *)

Definition out_type_error S :=
  out_ter S (res_throw builtin_type_error).

(** "Reference error" behavior *)

Definition out_ref_error S :=
  out_ter S (res_throw builtin_ref_error).

(** The "void" result is used by specification-level functions
    which do not produce any javascript value, but only perform
    side effects. (We return the value [undef] in the implementation.)
    -- TODO : sometimes we used false instead  -- where? fix it.. *)

Definition out_void S := 
  out_ter S undef.

(** [out_reject S bthrow] throws a type error if
    [bthrow] is true, else returns the value [false] *)

Definition out_reject S bthrow :=
  ifb bthrow = true 
    then (out_type_error S) 
    else (out_ter S false).

(** [out_ref_error_or_undef S bthrow] throws a type error if
    [bthrow] is true, else returns the value [undef] *)

Definition out_ref_error_or_undef S (bthrow:bool) :=
  if bthrow 
    then (out_ref_error S) 
    else (out_ter S undef).


(**************************************************************)
(** Constants used for tracing the use of [throw]/[strict] flags. *)

Definition throw_true : strictness_flag := true.
Definition throw_false : strictness_flag := false.
Definition throw_irrelevant : strictness_flag := false.


(**************************************************************)
(**************************************************************)
(**************************************************************)


(**************************************************************)
(** ** Auxiliary definition for the evaluation of a program code *)

(** Computing local variables of a statement or a program *)

(* TODO: problem below if we do Open Scope string_scope (why?).*) 
(* TODO: rename lx into xs *)
Fixpoint defs_stat (lx:list string) (t:stat) : (list string) :=
  let d := defs_stat lx in
  match t with
  | stat_expr e => nil
  | stat_seq p1 p2 => (d p1) ++ (d p2)
  | stat_var_decl y oe => ifb In y lx then nil else (y::nil)
  | stat_if e1 p2 None => d p2
  | stat_if e1 p2 (Some p3) => d p2 ++ d p3
  | stat_while e1 p2 => d p2
  | stat_with e1 p2 => d p2
  | stat_throw e1 => nil
  | stat_return eo1 => nil
  | stat_break => nil
  | stat_continue => nil
  | stat_try p1 None None => d p1 (* Should not happen. *)
  | stat_try p1 None (Some p3) => d p1 ++ d p3
  | stat_try p1 (Some (x,p2)) None => d p1 ++ d p2
  | stat_try p1 (Some (x,p2)) (Some p3) => d p1 ++ d p2 ++ d p3
  | stat_skip => nil
  | stat_for_in e1 e2 p => d p
  | stat_for_in_var x e1 e2 p => ifb In x lx then (d p) else (x::(d p)) 
  end.

Fixpoint defs_prog (lx:list string) p :=
  let d := defs_prog lx in
  match p with
  | prog_stat p => defs_stat lx p
  | prog_seq p1 p2 => d p1 ++ d p2
  | prog_function_decl _ _ _ => nil
  end.

(* TODO: the same thing for function declarations. *)


(**************************************************************)
(** ** Auxiliary definitions for reduction of [typeof] *)

Open Scope string_scope.

Definition typeof_prim w :=
  match w with
  | prim_undef => "undefined"
  | prim_null => "object"
  | prim_bool b => "boolean"
  | prim_number n => "number"
  | prim_string s => "string"
  end.


(**************************************************************)
(** ** Auxiliary definitions used for type conversions *)

(** Converts a number to a boolean *)

Definition convert_number_to_bool n :=
  ifb (n = JsNumber.zero \/ n = JsNumber.neg_zero \/ n = JsNumber.nan)
    then false
    else true.

(** Converts a string to a boolean *)

Definition convert_string_to_bool s :=
  ifb (s = "") then false else true.

(** Convert primitive to boolean *)

Definition convert_prim_to_boolean w :=
  match w with
  | prim_undef => false
  | prim_null => false
  | prim_bool b => b
  | prim_number n => convert_number_to_bool n
  | prim_string s => convert_string_to_bool s
  end.

Definition convert_value_to_boolean v :=
  match v with 
  | value_prim p => convert_prim_to_boolean p
  | value_object _ => true
  end.

(** Convert primitive to number *)

Definition convert_prim_to_number w :=
  match w with
  | prim_undef => JsNumber.nan
  | prim_null => JsNumber.zero
  | prim_bool b => if b then JsNumber.one else JsNumber.zero
  | prim_number n => n
  | prim_string s => JsNumber.from_string s
  end.

(** Convert number to integer *)

Definition convert_number_to_integer n :=
  ifb n = JsNumber.nan
    then JsNumber.zero
  else ifb (n = JsNumber.zero \/ n = JsNumber.neg_zero
       \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity)
    then n
  else
    JsNumber.mult (JsNumber.sign n) (JsNumber.floor (JsNumber.absolute n)).

(** Convert primitive to integer *)

Definition convert_primitive_to_integer w :=
  convert_number_to_integer (convert_prim_to_number w).

(** Convert bool to string *)

Definition convert_bool_to_string b := 
  if b then "true" else "false".

(** Convert primitive to string *)

Definition convert_prim_to_string w :=
  match w with
  | prim_undef => "undefined"
  | prim_null => "null"
  | prim_bool b => convert_bool_to_string b
  | prim_number n => JsNumber.to_string n
  | prim_string s => s
  end.

(* <informal> Implicit Types pref : preftype *)

(** Convert a preferred type to a string *)

Definition method_of_preftype pref :=
  match pref with
  | preftype_number => "valueOf"
  | preftype_string => "toString"
  end.

(** Return the opposite of a given prefered type *)

Definition other_preftypes pref :=
  match pref with
  | preftype_number => preftype_string
  | preftype_string => preftype_number
  end.

(**************************************************************)
(** ** Auxiliary functions for comparisons *)

 (** Abstract equality comparison for values of the same type *)

(*
Fixpoint value_equality_test_same_type T v1 v2 : bool :=
 let aux := value_equality_test in
   match T with
   | type_undef => true (* 1-a *)
   | type_null => true (* 1-b *)
   | type_number => (* 1-c *)
       match (v1, v2) with
       | (number_nan, _) => false 
       | (_, number_nan) => false 
       | (number_pos, number_neg_zero) => true 
       | (number_neg_zero, number_pos_zero) => true 
       | (_, _) => decide (v1 = v2) 
       end
   | type_string => decide (v1 = v2) 
   | type_bool => decide (v1 = v2) 
   | type_object => decide (v1 = v2).
*)
(** Strict Equality Operator *)
(*
Fixpoint value_strict_equality_test v1 v2 : bool :=
  let T1 := type_of v1 in 
  let T2 := type_of v2 in 
  if decide (T1 = T2)
            value_equality_test_same_type T1 v1 v2 
 else
   false.
*)
(** Definition of symCases *)
(*
Fixpoint sym_cases v1 v2 P1 P2 eq_n K :=
  let T1 := type_of v1 in 
  let T2 := type_of v2 in 
  if P1 T1 /\ P2 T2 eq_n v1 v2 else
    if P1 T2 /\ P2 T1 eq_n v2 v1 else K.
*)


(**************************************************************)
(** ** Implementation of [is_callable] *)

(** [is_callable S v fco] ensures that [fco] is [None]
    when [v] is not an object and, that [fco] is equal
    to the content of the call field of the object [v]
    otherwise. *)

Definition is_callable S v fco :=
  match v with
  | value_prim w => (fco = None)
  | value_object l => object_call S l fco
  end.


(**************************************************************)
(** ** Auxiliary definition used in the reduction of [get_own_property] *)

(** [object_get_own_property_builder A] is an auxilialry definition
    used by [object_get_own_property_impl os  l x An]. *)

Definition object_get_own_property_builder A :=
  let if_data {X:Type} (m:option X) (d:X) := 
    ifb prop_attributes_is_data A then Some (unsome_default d m) else None in
  let if_accessor {X:Type} (m:option X) (d:X) := 
    ifb prop_attributes_is_accessor A then Some (unsome_default d m) else None in
  {| prop_attributes_value := if_data (prop_attributes_value A) undef;
     prop_attributes_writable := if_data (prop_attributes_writable A) false;
     prop_attributes_get := if_accessor (prop_attributes_get A) undef;
     prop_attributes_set := if_accessor (prop_attributes_set A) undef;
     prop_attributes_enumerable := Some (unsome_default false (prop_attributes_enumerable A));
     prop_attributes_configurable := Some (unsome_default false (prop_attributes_configurable A)) |}.
  (* TODO: the spec is not very clear when A has a field value
     but not a field writable whether the result should have a
     writable field set to undefined or no writable field. The
     spec above formalizes the former assumption. *)

(** [object_get_own_property_impl P x An] is an auxilialry definition
    used by [object_get_own_property_default P x An]. *)

Inductive object_get_own_property_base : object_properties_type -> prop_name -> prop_descriptor -> Prop :=
  | object_get_own_property_impl_undef : forall P x,
      ~ Heap.indom P x ->
      object_get_own_property_base P x prop_descriptor_undef
  | object_get_own_property_impl_some : forall P x A A', 
      Heap.binds P x A ->
      A' = object_get_own_property_builder A ->
      object_get_own_property_base P x (prop_descriptor_some A').

(** [object_get_own_property_default S l x An] is an auxilialry definition
    used by [object_get_own_property S l x An]. *)

Definition object_get_own_property_default S l x An :=
  exists P, object_properties S l P 
         /\ object_get_own_property_base P x An.

(** [object_get_own_property S l x An] asserts that, in the state [S],
    a call to [get_own_property] on the object location [l] and the
    property name [x] returns the property descriptor [An]. Note that
    the location [l] provided cannot be null. Note also that the result
    [An] may be undefined. *)
    (* TODO: should the spec say that the function above always returns
       a fully populated descriptor or undefined, like it does for getproperty? *)

(* TODO:  To be moved on LibString in TLC *)
Fixpoint string_sub s (n l : int) : string :=
  substring (abs n) (abs l) s.

Inductive object_get_own_property : state -> object_loc -> prop_name -> prop_descriptor -> Prop := 
  | object_get_own_property_not_string : forall S l x An sclass,
      object_class S l sclass ->
      sclass <> "String" ->
      object_get_own_property_default S l x An ->
      object_get_own_property S l x An
  | object_get_own_property_string : forall S l x An An',
      object_class S l "String" ->
      object_get_own_property_default S l x An ->
      (If An <> prop_descriptor_undef 
       then An' = An 
       else
         (If (prim_string x <> convert_prim_to_string (prim_number (JsNumber.absolute (convert_primitive_to_integer x)))) (* TODO: remove coercion *) 
          then An' = prop_descriptor_undef
          else 
            (exists s, exists (i:int),
                 object_prim_value S l (prim_string s)
              /\ JsNumber.of_int i = convert_primitive_to_integer x
              /\ let len : int := String.length s in
                 If (len <= i) 
                 then An' = prop_descriptor_undef
                 else (let s' := string_sub s i 1 in
                       An' = prop_attributes_create_data s' false true false)
          )
      )) ->
      object_get_own_property S l x An'.


(**************************************************************)
(** ** Auxiliary definition used in the reduction of [get] *)

(** [object_get_property S l x An] asserts that, in the state [S],
    a call to [get] on the object location [l] and the property name [x]
    returns the property descriptor [An]. Note that [l] is actually
    of type [value] because it may be null. Note also that the result
    [An] may be undefined. *)

Inductive object_get_property : state -> value -> prop_name -> prop_descriptor -> Prop :=
  | object_get_prop_null : forall S x,
      object_get_property S null x prop_descriptor_undef
  | object_get_prop_some : forall S l x An,
      object_get_own_property S l x An ->
      An <> prop_descriptor_undef ->
      object_get_property S l x An
  | object_get_prop_undef : forall S l x lproto An,
      object_get_own_property S l x prop_descriptor_undef ->
      object_proto S l lproto ->
      object_get_property S lproto x An ->
      object_get_property S l x An.
      
Inductive object_all_properties : state -> value -> set prop_name -> Prop :=
  | object_all_properties_null : forall S,
      object_all_properties S null (@empty_impl prop_name)
  | object_all_properties_proto : forall obj S l lproto proto_properties,
      object_proto S l lproto ->
      object_all_properties S lproto proto_properties ->
      object_binds S l obj ->
      let obj_properties := Heap.dom (object_properties_ obj) in
      object_all_properties S (value_object l) (union_impl obj_properties proto_properties).

Inductive object_all_enumerable_properties : state -> value -> set prop_name -> Prop :=
  | object_all_enumerable_properties_intro : forall S l props,
       object_all_properties S l props ->
       let enumerable_props := inter_impl props (set_st (fun x => forall A,
           object_get_property S l x A /\
           prop_attributes_enumerable A = Some true
         )) in
       object_all_enumerable_properties S l enumerable_props.


(**************************************************************)
(** ** Auxiliary definition used in identifier resolution *)

(* [identifier_resolution C x] returns the extended expression
   which needs to be evaluated in order to perform the lookup
   of name [x] in the execution context [C]. Typically, a
   reduction rule that performs such a lookup would have a 
   premise of the form [red_expr S C (identifier_resolution C x) o1]. *)

Definition identifier_resolution C x := 
  let lex := execution_ctx_lexical_env C in
  let strict := execution_ctx_strict C in
  spec_lexical_env_get_identifier_ref lex x strict.

(**************************************************************)
(** ** Auxiliary definition used in the reduction of [eval] *)

(** Axiomatized parsing relation for eval *)

Axiom parse : string -> prog -> Prop.


(* TODO:  To be put in the Aux file. *)

Global Instance object_binds_pickable : forall S l,
  Pickable (object_binds S l).
Proof. typeclass. Qed.

Global Instance env_record_binds_pickable : forall S L,
  Pickable (env_record_binds S L).
Proof. typeclass. Qed.

