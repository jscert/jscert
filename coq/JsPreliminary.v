Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux.

(**************************************************************)
(** ** Implicit Types *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type B : builtin.
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
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
(** ** Auxiliary functions for results *)

(** Update the value field if it is empty *)

Definition res_overwrite_value_if_empty rv R :=
  If res_value R = resvalue_empty
    then res_with_value R rv
    else R.

(** Characterize results that is a reference *)

Inductive resvalue_is_ref : resvalue -> Prop :=
  | resvalue_is_ref_intro : forall r,
      resvalue_is_ref (resvalue_ref r).


(**************************************************************)
(** ** Auxiliary functions for function bodies *)

Definition funcbody_is_strict fb := 
  match fb with funcbody_intro (prog_intro b_strict _) _ => b_strict end.


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

(** Specification method that returns the type of a primitive *)

Definition type_of_prim w :=
   match w with
   | prim_undef => type_undef
   | prim_null => type_null
   | prim_bool _ => type_bool
   | prim_number _ => type_number
   | prim_string _ => type_string
   end.

(** Specification method that returns the type of a value *)

Definition type_of v :=
  match v with
  | value_prim w => type_of_prim w
  | value_object _ => type_object
  end.

(** Definition of the "SameValue" algorithm -- TODO: does not seem to be used *)

Definition value_same v1 v2 :=
  let T1 := type_of v1 in
  let T2 := type_of v2 in
  If T1 <> T2 then False else
  match T1 with
  | type_undef => True
  | type_null => True
  | type_number =>
      If   v1 = (prim_number JsNumber.nan)
         /\ v2 = (prim_number JsNumber.nan) then True
      else If    v1 = (prim_number JsNumber.zero)
              /\ v2 = (prim_number JsNumber.neg_zero) then False
      else If    v1 = (prim_number JsNumber.neg_zero)
              /\ v2 = (prim_number JsNumber.zero) then False
      else (v1 = v2)
  | type_string => (v1 = v2)
  | type_bool => (v1 = v2)
  | type_object => (v1 = v2)
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
   some_compare (fun b1 b2 => b1 <> b2).

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
     (L, object_write (state_intro cells bindings alloc) L O)
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
  
(** [object_get S l B] asserts that the
    [[get]] method for the object stored at address [l] 
    is described by specification function with identifier [B]. *)

Definition object_get S l B :=
  exists O, object_binds S l O /\ object_get_ O = B.  

(** [object_prim_value S l v] asserts that the primitive value
    field of the object stored at address [l] in [S] contains the
    value [v]. *)

Definition object_prim_value S l v :=
  exists O, object_binds S l O /\ object_prim_value_ O = Some v.

(** [object_call S l fco] asserts that the "primitive value"
    field of the object stored at address [l] in [S] contains
    an option [fco] which may contain function code. *)

Definition object_call S l fco :=
  exists O, object_binds S l O /\ object_call_ O = fco.

(** [object_has_instance S l Bo] asserts that the
    [[has instance]] method for the object stored at address [l] 
    is described by specification function with identifier [Bo]. *)

Definition object_has_instance S l Bo :=
  exists O, object_binds S l O /\ object_has_instance_ O = Bo.
  
(** [object_scope S l scope] asserts that the [[Scope]]
    field of the object stored at address [l] in [S] contains
    an option [scope] which may contain lexical environment. *)

Definition object_scope S l scope :=
  exists O, object_binds S l O /\ object_scope_ O = scope.

(** [object_formal_parameters S l fp] asserts that the [[FormalParameters]]
    field of the object stored at address [l] in [S] contains
    an option [fp] which may contain function formal parameters. *)

Definition object_formal_parameters S l fp :=
  exists O, object_binds S l O /\ object_formal_parameters_ O = fp.
  
(** [object_code S l bd] asserts that the [[Code]]
    field of the object stored at address [l] in [S] contains
    an option [bd] which may contain function funcbody. *)

Definition object_code S l bd :=
  exists O, object_binds S l O /\ object_code_ O = bd.

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

(* LATER: get rid of "prop_attributes_create_accessor" and use everywhere
   the function below which is slightly more general *)
Definition prop_attributes_create_accessor_opt vseto vgeto be bc := {|
   prop_attributes_value := None;
   prop_attributes_writable := None;
   prop_attributes_get := vgeto;
   prop_attributes_set := vseto;
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
  
Definition ref_is_value r v :=
  ref_base r = ref_base_type_value v.

(** [ref_is_env_record r L] asserts that the reference [r]
    either has the environment record L as base. *)

Definition ref_is_env_record r L :=
  ref_base r = ref_base_type_env_loc L.

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

(** [valid_lhs_for_assign R] asserts that [R] will not satisfy
    the condition under which a SyntaxError gets triggered
    (see the semantics of simple assignement in the spec).
    LATER: will be used if we do not rely on parser for raising
    the SyntaxError. *)

Open Scope string_scope. (* TODO: move to top of the file *)

(* LATER: only for syntax errors
Definition valid_lhs_for_assign R :=
  ~ (exists r,
         R = ret_ref r
      /\ ref_strict r = true
      /\ ref_kind_of r = ref_kind_env_record
      /\ let s := ref_name r in
         (s = "eval" \/ s = "arguments")).
*)

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

(** Definition of a lexical context with the global environment *)

Definition lexical_env_initial : lexical_env :=
  (env_loc_global_env_record)::nil.

(** Definition of the initial execution context *)

Definition execution_ctx_initial str :=
  {| execution_ctx_lexical_env := lexical_env_initial;
     execution_ctx_variable_env := lexical_env_initial;
     execution_ctx_this_binding := builtin_global;
     execution_ctx_strict := str |}.


(**************************************************************)
(** Grammar of preferred types for use by the default_value
    conversion. *)

Inductive preftype :=
  | preftype_number
  | preftype_string.

Implicit Type pref : preftype.

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
(** Constants used for tracing the use of [throw]/[strict] flags. *)

Definition throw_true : strictness_flag := true.
Definition throw_false : strictness_flag := false.
Definition throw_irrelevant : strictness_flag := false.


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

(** Convert boolean to string *)

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


(**************************************************************)
(** ** Auxiliary functions for comparisons *)

(** Abstract equality comparison for values of the same type.
    (the code assumes [v1] and [v2] to both have type [T].) *)

Definition equality_test_for_same_type T v1 v2 :=
  match T with
  | type_undef => true
  | type_null => true
  | type_number =>
     match v1,v2 with
     | value_prim (prim_number n1), value_prim (prim_number n2) =>
       ifb n1 = JsNumber.nan then false
       else ifb n2 = JsNumber.nan then false
       else ifb n1 = JsNumber.zero /\ n2 = JsNumber.neg_zero then true
       else ifb n1 = JsNumber.neg_zero /\ n2 = JsNumber.zero then true
       else decide (n1 = n2)
     | _,_ => false (* this case never happens, by assumption *)
     end
  | type_string => decide (v1 = v2)
  | type_bool => decide (v1 = v2)
  | type_object => decide (v1 = v2)
  end.

(** Strict equality comparison *)

Definition strict_equality_test v1 v2 :=
  let T1 := type_of v1 in
  let T2 := type_of v2 in
  ifb T1 = T2
    then equality_test_for_same_type T1 v1 v2
    else false.

(** Inequality comparison for numbers *)

Definition inequality_test_number n1 n2 : prim :=
  ifb n1 = JsNumber.nan \/ n2 = JsNumber.nan then prim_undef
  else ifb n1 = n2 then false
  else ifb n1 = JsNumber.zero /\ n2 = JsNumber.neg_zero then false
  else ifb n1 = JsNumber.neg_zero /\ n2 = JsNumber.zero then false
  else ifb n1 = JsNumber.infinity then false
  else ifb n2 = JsNumber.infinity then true
  else ifb n2 = JsNumber.neg_infinity then false
  else ifb n1 = JsNumber.neg_infinity then true
  else JsNumber.lt_bool n1 n2.

(** Inequality comparison for strings e*)

Fixpoint inequality_test_string s1 s2 : bool :=
  match s1, s2 with
  | _, EmptyString => false
  | EmptyString, String _ _ => true
  | String c1 s1', String c2 s2' =>
     ifb c1 = c2
       then inequality_test_string s1' s2'
       else decide (int_of_char c1 < int_of_char c2)
  end.

(** Inequality comparison *)

Definition inequality_test_primitive w1 w2 : prim :=
  match w1, w2 with
  | prim_string s1, prim_string s2 => inequality_test_string s1 s2
  | _, _ => inequality_test_number (convert_prim_to_number w1) (convert_prim_to_number w2)
  end.


(**************************************************************)
(** ** Factorization of rules for unary operators *)

(* TODO: move a bunch of these defs into js_pretty_inter *)

(** Operations increment and decrement *)

Definition add_one n :=
  JsNumber.add n JsNumber.one.

Definition sub_one n :=
  JsNumber.sub n JsNumber.one.

(** Relates a binary operator [++] or [--] with the value
    +1 or -1 and with a boolean that indicates whether the
    operator is prefix (in which case the updated value should
    be returned by the semantics). *)

Inductive prepost_op : unary_op -> (number -> number) -> bool -> Prop :=
  | prepost_op_pre_incr : prepost_op unary_op_pre_incr add_one true
  | prepost_op_pre_decr : prepost_op unary_op_pre_decr sub_one true
  | prepost_op_post_incr : prepost_op unary_op_post_incr add_one false
  | prepost_op_post_decr : prepost_op unary_op_post_decr sub_one false.

(** Characterization of unary "prepost" operators. *)

(* TODO: change def below into 
   prepost_unary_op op := exists f b, prepost_op op f b. 
   and even remove this definition if it is not used *)

Definition prepost_unary_op op :=
  match op with
  | unary_op_post_incr
  | unary_op_post_decr
  | unary_op_pre_incr
  | unary_op_pre_decr => True
  | _ => False
  end.

(** Characterization of unary operators that start by
    evaluating and calling get_value on their argument. *)

Definition regular_unary_op op :=
  match op with
  | unary_op_typeof => False
  | _ => If prepost_unary_op op
           then False
           else True
  end.

(**************************************************************)
(** ** Factorization of rules for binary operators *)

(* TODO: move a bunch of these defs into js_pretty_inter *)

(** Characterizes pure mathematical operators, which always call toNumber
    before applying a mathematical function *)

Inductive puremath_op : binary_op -> (number -> number -> number) -> Prop := 
  | puremath_op_mult : puremath_op binary_op_mult JsNumber.mult
  | puremath_op_div : puremath_op binary_op_div JsNumber.div
  | puremath_op_mod : puremath_op binary_op_mod JsNumber.fmod
  | puremath_op_sub : puremath_op binary_op_sub JsNumber.sub.

(** Characterizes bitwise operators, which always call toInt32
    before applying a mathematical function *)

Inductive bitwise_op : binary_op -> (int -> int -> int) -> Prop := 
  | bitwise_op_and : bitwise_op binary_op_bitwise_and JsNumber.int32_bitwise_and
  | bitwise_op_or : bitwise_op binary_op_bitwise_or JsNumber.int32_bitwise_or
  | bitwise_op_xor : bitwise_op binary_op_bitwise_xor JsNumber.int32_bitwise_xor.

(** Characterizes shift operators, and tell whether they are
    signed or unsigned, and to the corresponding mathematical function *)

Inductive shift_op : binary_op -> bool -> (int -> int -> int) -> Prop := 
  | shift_op_left_shift : shift_op binary_op_left_shift false JsNumber.int32_left_shift
  | shift_op_right_shift : shift_op binary_op_right_shift false JsNumber.int32_right_shift
  | shift_op_unsigned_right_shift : shift_op binary_op_unsigned_right_shift true JsNumber.uint32_right_shift.

(** Characterizes inequality operators, which are all similar to [lt], 
    up to two parameters: (1) whether arguments should be swapped
    and (2) whether the result should be negated. *)

Inductive inequality_op : binary_op -> bool -> bool -> Prop := 
  | inequality_op_lt : inequality_op binary_op_lt false false 
  | inequality_op_gt : inequality_op binary_op_lt true false  
  | inequality_op_le : inequality_op binary_op_lt true true 
  | inequality_op_ge : inequality_op binary_op_lt false true.

(** Characterizes lazy binary operators (&& and ||),
    and the boolean value for which the first operand triggers 
    an immediate return *)

Inductive lazy_op : binary_op -> bool -> Prop := 
  | lazy_op_and : lazy_op binary_op_and false
  | lazy_op_or : lazy_op binary_op_or true.

(** Characterization of binary operators that start by 
    evaluating and calling get_value on both of their 
    arguments. *)

Definition regular_binary_op op :=
  match op with
  | binary_op_and
  | binary_op_or => False
  | _ => True
  end.
  (* TODO: use alternative definition below
      ~ (exists b, lazy_op op b). *)


(**************************************************************)
(** ** Implementation of [callable] *)

(** [callable S v Bo] ensures that [Bo] is [None]
    when [v] is not an object and, that [Bo] is equal
    to the content of the call field of the object [v]
    otherwise. *)

Definition callable S v Bo :=
  match v with
  | value_prim w => (Bo = None)
  | value_object l => object_call S l Bo
  end.

(** [is_callable S v] asserts that the object [v] is a location
    describing an object with a Call method. *)

Definition is_callable S v :=
  exists B, callable S v (Some B).


(**************************************************************)
(** ** Auxiliary definitions for reduction of [typeof] *)

Open Scope string_scope.

(** [typeof] for a primitive *)

Definition typeof_prim w :=
  match w with
  | prim_undef => "undefined"
  | prim_null => "object"
  | prim_bool b => "boolean"
  | prim_number n => "number"
  | prim_string s => "string"
  end.

(** [typeof] for a value *)

Definition typeof_value S v :=
  match v with
  | value_prim w => typeof_prim w
  | value_object l => If is_callable S l then "function" else "object"
  end.


(**************************************************************)
(** ** Auxiliary definition used in the reduction of [get_own_property] *)

(** [object_get_own_property_builder A] is an auxiliary definition
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


(** [object_get_own_property_base P x An] is an auxilialry definition
    used by [object_get_own_property_default P x An]. *)

Inductive object_get_own_property_base : object_properties_type -> prop_name -> prop_descriptor -> Prop :=
  | object_get_own_property_base_undef : forall P x,
      ~ Heap.indom P x ->
      object_get_own_property_base P x prop_descriptor_undef
  | object_get_own_property_base_some : forall P x A A',
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

(* TODO: double check this definition *)

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
          else (* TODO: make an auxiliary definition for this else branch *)
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

(* TODO: add comment / fix def *)

Inductive object_all_properties : state -> value -> set prop_name -> Prop :=
  | object_all_properties_null : forall S,
      object_all_properties S null (@empty_impl prop_name)
  | object_all_properties_proto : forall obj S l lproto proto_properties,
      object_proto S l lproto ->
      object_all_properties S lproto proto_properties ->
      object_binds S l obj ->
      let obj_properties := Heap.dom (object_properties_ obj) in
      object_all_properties S (value_object l) (union_impl obj_properties proto_properties).

(* TODO: add comment / fix def  *)

Inductive object_all_enumerable_properties : state -> value -> set prop_name -> Prop :=
  | object_all_enumerable_properties_intro : forall S l props,
       object_all_properties S l props ->
       let enumerable_props := inter_impl props (set_st (fun x => forall A,
           object_get_property S l x A /\
           prop_attributes_enumerable A = Some true
         )) in
       object_all_enumerable_properties S l enumerable_props.


(**************************************************************)
(** ** Auxiliary definition used by object initializers *)

Definition string_of_propname (pn : propname) : prop_name :=
  match pn with 
  | propname_identifier s => s
  | propname_string s => s
  | propname_number n => JsNumber.to_string n
  end.


(**************************************************************)
(** ** Auxiliary definition used in the reduction of [eval] *)

(** Axiomatized parsing relation for eval *)

Axiom parse : string -> prog -> Prop.


