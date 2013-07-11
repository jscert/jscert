Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux.
Open Scope string_scope.

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
(*Implicit Type B : builtin.*)
Implicit Type ty : type.

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
(** ** Auxiliary functions for results *)

(** Update the value field if it is empty *)

Definition res_overwrite_value_if_empty rv R :=
  ifb res_value R = resvalue_empty
    then res_with_value R rv
    else R.

(** Characterize results that is a reference *)

Inductive resvalue_is_ref : resvalue -> Prop :=
  | resvalue_is_ref_intro : forall r,
      resvalue_is_ref (resvalue_ref r).

(** Asserts that a result contains a label that belongs to a set *)

Definition res_label_in R labs := label_set_mem (res_label R) labs.


(**************************************************************)
(** ** Auxiliary functions on values and types *)

(** Convert a literal into a primitive (11.1.3 and 7.8) *)

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

(** Specification method that returns the type of a primitive (8) *)

Definition type_of_prim w :=
   match w with
   | prim_undef => type_undef
   | prim_null => type_null
   | prim_bool _ => type_bool
   | prim_number _ => type_number
   | prim_string _ => type_string
   end.

(** Specification method that returns the type of a value (8) *)

Definition type_of v :=
  match v with
  | value_prim w => type_of_prim w
  | value_object _ => type_object
  end.

(** Definition of the "SameValue" algorithm, which appears to
    be equivalent to logical equality. The spec states:

    Definition value_same v1 v2 :=
      let ty1 := type_of v1 in
      let ty2 := type_of v2 in
      ifb ty1 <> ty2 then False else
      match ty1 with
      | type_undef => True
      | type_null => True
      | type_number =>
          ifb   v1 = (prim_number JsNumber.nan)
             /\ v2 = (prim_number JsNumber.nan) then True
          else ifb    v1 = (prim_number JsNumber.zero)
                  /\ v2 = (prim_number JsNumber.neg_zero) then False
          else ifb    v1 = (prim_number JsNumber.neg_zero)
                  /\ v2 = (prim_number JsNumber.zero) then False
          else (v1 = v2)
      | type_string => (v1 = v2)
      | type_bool => (v1 = v2)
      | type_object => (v1 = v2)
      end.

    Which is equivalent to:
*)
(* TODO: problem of the several representations of NaN *)

Definition same_value v1 v2 := (v1 = v2).

(**************************************************************)
(** ** Operations on event lists *)

(** Add an event to the list *)

Definition state_with_new_event S new_event :=
  match S with
    | state_intro ob_heap env_heap fresh_locs ev_list =>
      state_intro ob_heap env_heap fresh_locs (new_event::ev_list)
  end.


(**************************************************************)
(** ** Operations on objects *)

(** Update the state by updating the object heap *)

Definition state_with_object_heap S new_object_heap :=
   match S with
   | state_intro old_object_heap env_heap fresh_locs ev_list =>
     state_intro new_object_heap env_heap fresh_locs ev_list
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
   match S with state_intro cells bindings (n:::alloc) ev_list =>
     let L := object_loc_normal n in
     (L, object_write (state_intro cells bindings alloc ev_list) L O)
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

(** [object_extensible S l b] asserts that the extensible field
    of the object stored at address [l] in [S] contains the
    value [b]. *)

Definition object_extensible S l b :=
  exists O, object_binds S l O /\ object_extensible_ O = b.

(** [object_prim_value S l v] asserts that the primitive value
    field of the object stored at address [l] in [S] contains the
    value [v]. *)

Definition object_prim_value S l v :=
  exists O, object_binds S l O /\ object_prim_value_ O = Some v.

(** [object_get S l B] asserts that the
    [[get]] method for the object stored at address [l] 
    is described by specification function with identifier [B]. *)
(* TODO: remove this def and use the general case below *)

Definition object_get S l B :=
  exists O, object_binds S l O /\ object_get_ O = B.  

(** Generalization of the above -- TODO:
    Note that a number of the fct below are deprecated... *)

Definition object_method (X:Type) Proj S l (B:X) :=
  exists O, object_binds S l O /\ Proj O = B.

(** [object_call S l fco] asserts that the "primitive value"
    field of the object stored at address [l] in [S] contains
    an option [fco] which may contain function code. *)

Definition object_call S l fco :=
  exists O, object_binds S l O /\ object_call_ O = fco.
  
(** [object_construct S l fco] asserts that the "construct"
    field of the object stored at address [l] in [S] contains
    an option [fco] which may contain code. *)

Definition object_construct S l fco :=
  exists O, object_binds S l O /\ object_construct_ O = fco.

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
  
(** [object_parameter_map S l lmap] asserts that the [[ParameterMap]]
    field of the object stored at address [l] in [S] contains
    an option [lmap] which may contain a location to a parameter map object. *)

Definition object_parameter_map S l lmap :=
  exists O, object_binds S l O /\ object_parameter_map_ O = lmap.

(** [object_properties S l P] asserts that [P]
    is the content of the properties field of the object
    stored at address [l] in [S]. *)

Definition object_properties S l P :=
  exists O, object_binds S l O /\ object_properties_ O = P.

(** [object_properties_keys_as_list S l xs] asserts that [xs]
    is the list of property names associated to the object
    stored at address [l] in [S] (the list can be in any order). *)

Definition object_properties_keys_as_list S l xs :=
  exists P, object_properties S l P /\ heap_keys_as_list P xs.

(** [object_properties_enumerable_keys_as_list S l xs] asserts that [xs]
    is the list of enumerable property names associated to the object
    stored at address [l] in [S] (the list can be in any order). *)

Definition object_properties_enumerable_keys_as_list S l xs :=
  (* !!!
  
   !!! 
  
   !!!!
   
   !!!  TODO: fix the definition to the real thing *)
  exists P, object_properties S l P /\ heap_keys_as_list P xs.

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

(** [object_heap_set_extensible_false S l S'] asserts that the state
    [S] contains an object at location [l], and that [S']
    describes the heap after the object at location [l] has
    been updated by settin its [extensible] internal property to false *)
(* TODO: we need something more general? (i.e. giving a boolean as an arg?*)

Definition object_heap_set_extensible b S l S' :=
  exists O, object_binds S l O
         /\ S' = object_write S l (object_set_extensible O b).

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

(** [search_proto_chain S l x res] Asserts that the result of
searching the prototype chain of l in S for a field named x will be
res. If it finds it, we get Some result, otherwise None *)

(* Daniele: moved to JSPrettyRules
Inductive search_proto_chain : state -> object_loc -> prop_name -> option object_loc -> Prop :=
  | search_proto_chain_found : forall S l x,
                                 object_has_property S l x ->
                                 search_proto_chain S l x (Some l)
  | search_proto_chain_not_found : forall S l x,
                                     not (object_has_property S l x) ->
                                     object_proto S l prim_null ->
                                     search_proto_chain S l x None
  | search_proto_chain_inductive : forall S l x v l' res,
                                     (not (object_has_property S l x) ->
                                     object_proto S l (value_object l') ->
                                     search_proto_chain S l' x res ->
                                     search_proto_chain S l x res).
*)

(** [make_delete_event S l x ev] constructs a delete_event "ev" which
records the deletion of the property (l,x) in the state S. *)

(* Daniele: moved to JSPrettyRules
Inductive make_delete_event : state -> object_loc -> prop_name -> event -> Prop :=
  | make_delete_event_intro : forall S l x res ev,
                                search_proto_chain S l x res ->
                                ev = delete_event l x res ->
                                make_delete_event S l x ev.
*)

(** [object_rem_property S l x A] removes from the object stored
    at address [l] in [S] the property named [x]; The operation
    returns the updated state. *)

Definition object_rem_property S l x S' :=
  object_heap_map_properties S l (fun P => Heap.rem P x) S'.
  
(** Smart constructor for building a new object with the default 
    behavior of the get method, and the extensible property to true. *)

Definition object_new vproto sclass :=
  object_create vproto sclass true Heap.empty.


(**************************************************************)
(** ** Auxiliary definitions for attributes *)

(** True is its argument is a data *)

(* In practice, this function is used as [attributes_is_data A = true] using an implicit [isTrue]:  wouldn't it be better if it were a boolean instead of a proposition? -- Martin. 
   TODO: can't we simply use pattern matching instead? *)

Definition attributes_is_data A : Prop := 
  match A with
  | attributes_data_of Ad => True
  | attributes_accessor_of Aa => False
  end.

(** Returns the value of the writable field of an attribute *)

Definition attributes_writable A : bool :=
  match A with
  | attributes_data_of Ad => attributes_data_writable Ad
  | attributes_accessor_of Aa => false
  end.
(* TODO: check:  Even if it's used in the semantics, is that wanted? -- Martin *)


(**************************************************************)
(** ** Smart constructors for property attributes *)

(** Constructs a named data property attributes
    for a constant value *)

Definition attributes_data_intro_constant v :=
   attributes_data_intro v false false false.

(** Constructs a named data property attributes
    for a writable value *)

Definition attributes_data_intro_writable v :=
   attributes_data_intro v true false false.

(** Constructs a named data property attributes
    for a writable and configurable value *)

Definition attributes_data_intro_configurable v :=
   attributes_data_intro v true false true.

(** Constructs a named data property attributes
    for a writable and configurable, enumerable value *)

Definition attributes_data_intro_all_true v :=
   attributes_data_intro v true true true.

(**************************************************************)
(** ** Smart constructors for accessor attributes *)

Definition attributes_accessor_intro_all_true v :=
   attributes_accessor_intro v true true true.


(**************************************************************)
(** ** Smart constructors for property descriptors *)

(** Builds a property descriptor that corresponds to a fully-populated data descriptor *)

Definition descriptor_intro_data v bw be bc := 
  {| descriptor_value := Some v;
     descriptor_writable := Some bw;
     descriptor_get := None;
     descriptor_set := None;
     descriptor_enumerable := Some be;
     descriptor_configurable := Some bc |}.

(** Builds a property descriptor that corresponds to a fully-populated accessor descriptor;
    with optional getter and setter fields. *)

Definition descriptor_intro_accessor vg vs be bc := 
  {| descriptor_value := None;
     descriptor_writable := None;
     descriptor_get := Some vg;
     descriptor_set := Some vs;
     descriptor_enumerable := Some be;
     descriptor_configurable := Some bc |}.

(** Builds an empty property descriptor --used by ToPropertyDescriptor (8.10.5) *)

Definition descriptor_intro_empty := 
  {| descriptor_value := None;
     descriptor_writable := None;
     descriptor_get := None;
     descriptor_set := None;
     descriptor_enumerable := None;
     descriptor_configurable := None |}.

(** Tests whether a descriptor has incompatible fields --used by ToPropertyDescriptor (8.10.5) *)

Definition descriptor_inconsistent Desc :=
     (descriptor_get Desc <> None \/ descriptor_set Desc <> None)
  /\ (descriptor_value Desc <> None \/ descriptor_writable Desc <> None).


(**************************************************************)
(** ** Classification of property descriptors (8.10) *)

(** Characterization of data descriptors *)

Definition descriptor_is_data Desc :=
  ~ (descriptor_value Desc = None /\ descriptor_writable Desc = None).

(** Characterization of accessor descriptors *)

Definition descriptor_is_accessor Desc :=
  ~ (descriptor_get Desc = None /\ descriptor_set Desc = None).

(** Characterization of generic descriptors,
    which could also be defined as:
         descriptor_value Desc = None 
      /\ descriptor_writable Desc = None
      /\ descriptor_get Desc = None 
      /\ descriptor_set Desc = None. *)

Definition descriptor_is_generic Desc :=
  (~ descriptor_is_data Desc) /\ (~ descriptor_is_accessor Desc).


(**************************************************************)
(** ** Conversion used in the semantics of DefinedOwnProperty *)

(** Default data property attributes *)

Definition attributes_data_default := {|
   attributes_data_value := undef;
   attributes_data_writable := false;
   attributes_data_enumerable := false;
   attributes_data_configurable := false |}.

(** Default accessor property attributes *)

Definition attributes_accessor_default := {|
   attributes_accessor_get := undef;
   attributes_accessor_set := undef;
   attributes_accessor_enumerable := false;
   attributes_accessor_configurable := false |}.

(** Convert a data property attributes into an accessor property attributes *)

Definition attributes_accessor_of_attributes_data Ad := {|
   attributes_accessor_get := attributes_accessor_get attributes_accessor_default;
   attributes_accessor_set := attributes_accessor_set attributes_accessor_default;
   attributes_accessor_enumerable := attributes_data_enumerable Ad;
   attributes_accessor_configurable := attributes_data_configurable Ad |}.

(** Convert an accessor property attributes into a data property attributes *)

Definition attributes_data_of_attributes_accessor Aa := {|
   attributes_data_value := attributes_data_value attributes_data_default;
   attributes_data_writable := attributes_data_writable attributes_data_default;
   attributes_data_enumerable := attributes_accessor_enumerable Aa;
   attributes_data_configurable := attributes_accessor_configurable Aa |}.

(** Updates a data property attributes with a property descriptor *)

Definition attributes_data_update Ad Desc := {|
   attributes_data_value := unsome_default (attributes_data_value Ad) (descriptor_value Desc);
   attributes_data_writable := unsome_default (attributes_data_writable Ad) (descriptor_writable Desc);
   attributes_data_enumerable := unsome_default (attributes_data_enumerable Ad) (descriptor_enumerable Desc);
   attributes_data_configurable := unsome_default (attributes_data_configurable Ad) (descriptor_configurable Desc) |}.

(** Updates an accessor property attributes with a property descriptor *)

Definition attributes_accessor_update Aa Desc := {|
   attributes_accessor_get := unsome_default (attributes_accessor_get Aa) (descriptor_get Desc);
   attributes_accessor_set := unsome_default (attributes_accessor_set Aa) (descriptor_set Desc);
   attributes_accessor_enumerable := unsome_default (attributes_accessor_enumerable Aa) (descriptor_enumerable Desc);
   attributes_accessor_configurable := unsome_default (attributes_accessor_configurable Aa) (descriptor_configurable Desc) |}.

(** Updates a property attributes with a property descriptor *)

Definition attributes_update A Desc : attributes := 
  match A with
  | attributes_data_of Ad => attributes_data_update Ad Desc
  | attributes_accessor_of Aa => attributes_accessor_update Aa Desc
  end.

(** Converts a property descriptor into a data property attributes  *)

Definition attributes_data_of_descriptor Desc :=
  attributes_data_update attributes_data_default Desc.

(** Converts a property descriptor into an accessor property attributes  *)

Definition attributes_accessor_of_descriptor Desc :=
  attributes_accessor_update attributes_accessor_default Desc.

(** Converts a property attributes into an property descriptor *)

Definition descriptor_of_attributes A :=
  match A with
  | attributes_data_of Ad =>
    {| descriptor_value := Some (attributes_data_value Ad);
       descriptor_writable := Some (attributes_data_writable Ad);
       descriptor_get := None;
       descriptor_set := None;
       descriptor_enumerable := Some (attributes_data_enumerable Ad);
       descriptor_configurable := Some (attributes_data_configurable Ad) |}
  | attributes_accessor_of Aa =>
    {| descriptor_value := None;
       descriptor_writable := None;
       descriptor_get := Some (attributes_accessor_get Aa);
       descriptor_set := Some (attributes_accessor_set Aa);
       descriptor_enumerable := Some (attributes_accessor_enumerable Aa);
       descriptor_configurable := Some (attributes_accessor_configurable Aa) |}
  end.

(* Coercion associated to [descriptor_of_attributes] *)

Coercion descriptor_of_attributes : attributes >-> descriptor.


(**************************************************************)
(** ** Type [attributes] *)

(** Returns the value of the configurable field of an attribute *)

Definition attributes_configurable A :=
  match A with
  | attributes_data_of Ad => attributes_data_configurable Ad
  | attributes_accessor_of Aa => attributes_accessor_configurable Aa
  end.

(** Returns the value of the enumerable field of an attribute *)

Definition attributes_enumerable A :=
  match A with
  | attributes_data_of Ad => attributes_data_enumerable Ad
  | attributes_accessor_of Aa => attributes_accessor_enumerable Aa
  end.

(** Modifies the configurable field of an attribute *)

Definition attributes_with_configurable A bc' :=
  match A with
  | attributes_data_of Ad => attributes_data_of (attributes_data_with_configurable Ad bc')
  | attributes_accessor_of Aa => attributes_accessor_of (attributes_acccessor_with_configurable Aa bc')
  end.


(**************************************************************)
(** ** Auxiliary definitions for reduction of [get_own_property]  *)

(** The following definitions are used to define when
    a property descriptor contains another one. *)

Definition if_some_then_same (A:Type) F (oldval newval : option A) :=
  match newval, oldval with
  | Some v1, Some v2 => F v1 v2
  | Some v1, None => False
  | None, _ => True
  end.

Definition if_some_value_then_same :=
  if_some_then_same same_value.

Definition if_some_bool_then_same :=
  if_some_then_same (@eq bool).

Definition descriptor_contains Desc_old Desc_new :=
  match Desc_old, Desc_new with
  | descriptor_intro ov ow og os oe oc,
    descriptor_intro nv nw ng ns ne nc =>
       if_some_value_then_same ov nv
    /\ if_some_bool_then_same ow nw
    /\ if_some_value_then_same og ng
    /\ if_some_value_then_same os ns
    /\ if_some_bool_then_same oe ne
    /\ if_some_bool_then_same oc nc
  end.

(** The following definitions are used below. *)

Definition descriptor_enumerable_not_same A Desc :=
   match descriptor_enumerable Desc with
   | None => False 
   | Some b => b <> (attributes_enumerable A)
   end.

Definition descriptor_value_not_same Ad Desc :=
   match descriptor_value Desc with
   | None => False
   | Some v => ~ same_value v (attributes_data_value Ad)
   end.

Definition descriptor_get_not_same Aa Desc :=
   match descriptor_get Desc with
   | None => False
   | Some v => ~ same_value v (attributes_accessor_get Aa)
   end.

Definition descriptor_set_not_same Aa Desc :=
   match descriptor_set Desc with
   | None => False
   | Some v => ~ same_value v (attributes_accessor_set Aa)
   end.

(** The following definitions are used to describe the
    cases in which the DefineOwnProperty specification method
    performs an illegal operation. *)

Definition attributes_change_enumerable_on_non_configurable A Desc : Prop := (* 8.12.9 step 7 *)
     attributes_configurable A = false
  /\ (   (descriptor_configurable Desc = Some true)
      \/ (descriptor_enumerable_not_same A Desc)).

Definition attributes_change_data_on_non_configurable Ad Desc : Prop := (* 8.12.9 step 10.a *)
     attributes_configurable Ad = false
  /\ attributes_data_writable Ad = false
  /\ (   descriptor_writable Desc = Some true
      /\ descriptor_value_not_same Ad Desc).

Definition attributes_change_accessor_on_non_configurable Aa Desc : Prop := (* 8.12.9 step 11.a *)
     attributes_configurable Aa = false
  /\ (   descriptor_get_not_same Aa Desc
      \/ descriptor_set_not_same Aa Desc).


(**************************************************************)
(** ** Auxiliary definitions for reduction of [has_instance]  *)

(** Characterize the case where an error is thrown (15.3.5.4, step 2) *)

Definition spec_function_get_error_case S x v := 
  x = "caller" /\ exists l bd, 
    v = value_object l /\ object_code S l (Some bd) /\ funcbody_is_strict bd = true.


(**************************************************************)
(** ** Auxiliary functions on references (8.7) *)

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
  \/ k = ref_kind_null
  \/ k = ref_kind_object.
  
Definition ref_is_value r v :=
  ref_base r = ref_base_type_value v.

(** [ref_is_env_record r L] asserts that the reference [r]
    either has the environment record L as base. *)

Definition ref_is_env_record r L :=
  ref_base r = ref_base_type_env_loc L.

(** [ref_is_unresolvable r] asserts that the reference [r]
    has [undef] as base. *)

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
(** ** Operations on environment records (10.2) *)

(** Update the state by updating the environment record heap *)

Definition state_with_env_record_heap S new_env_heap :=
   match S with
   | state_intro object_heap old_env_heap fresh_locs ev_list =>
     state_intro object_heap new_env_heap fresh_locs ev_list
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
   match S with state_intro cells bindings (L:::alloc) ev_list =>
     let bindings' := Heap.write bindings L E in
     (L, state_intro cells bindings' alloc ev_list)
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
(** ** Operations on declarative environments (10.2) *)

(** The empty declarative environment *)

Definition decl_env_record_empty : decl_env_record :=
  Heap.empty.

(** [decl_env_record_binds Ed x mu v] asserts that the
    declarative environment [Ed] maps the property name
    [x] to the value [v] with the mutability flag [mu] *)

Definition decl_env_record_binds Ed x (mu : mutability) v :=
  Heap.binds Ed x (mu, v).

(** [decl_env_record_indom Ed x] asserts that the
    declarative environment [Ed] binds the property name [x]. *)

Definition decl_env_record_indom Ed x :=
  Heap.indom (Ed:decl_env_record) x.

(** [decl_env_record_write Ed x mu v] returns an updated
    declarative enviromnent with a new binding from [x] to
    [v] with mutability flag [mu]. *)

Definition decl_env_record_write Ed x mu v : decl_env_record :=
  Heap.write Ed x (mu, v).

(** [decl_env_record_rem Ed x] returns an updated declarative
    enviromnent with a new binding for [x] removed. *)

Definition decl_env_record_rem Ed x : decl_env_record :=
  Heap.rem (Ed:decl_env_record) x.

(** TODO: Change the following definition to a relation. *)

Definition env_record_write_decl_env S L x mu v :=
  match Heap.read (state_env_record_heap S) L with
  | env_record_decl Ed =>
     let env' := decl_env_record_write Ed x mu v in
     env_record_write S L (env_record_decl env')
  | env_record_object _ _ => S (* It should never happen *)
  end.


(**************************************************************)
(** ** Operations on lexical environments (10.2) *)

(** [lexical_env_alloc S lex E] returns a pair [(lex',S')]
    made of lexical environment [le'] that extends the
    lexical environment [lex] with a environment record
    location [L], which, in the updated state [S'],
    is bound to an environment record [E]. *)

Definition lexical_env_alloc S lex E :=
  let (L, S') := env_record_alloc S E in
  let lex' := (L::lex) in
  (lex', S').

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
(** ** Operations on execution contexts (10.3) *)

(** A smart constructor for execution contexts whose variable
    context is identical to their lexical context. *)

Definition execution_ctx_intro_same X lthis strict :=
  execution_ctx_intro X X lthis strict.

(** A smart constructor for modifying the lexical environment
    of an execution context. *)

Definition execution_ctx_with_lex C lex :=
  match C with execution_ctx_intro x1 x2 x3 x4 =>
    execution_ctx_intro lex x2 x3 x4 end.
    
(** A smart constructor for modifying the lexical environment
    and variable environment are the same *)

Definition execution_ctx_with_lex_same C lex :=
  match C with execution_ctx_intro x1 x2 x3 x4 =>
    execution_ctx_intro lex lex x3 x4 end.

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
     execution_ctx_this_binding := prealloc_global;
     execution_ctx_strict := str |}.


(**************************************************************)
(** Grammar of preferred types for use by the defaultValue
    conversion. *)

(** A prefered type for defaultValue is either "number" or "string" *)

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
(** ** Auxiliary definitions used for type conversions (9) *)

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

(** Convert a value to a boolean (9.2) *)

Definition convert_value_to_boolean v :=
  match v with
  | value_prim p => convert_prim_to_boolean p
  | value_object _ => true
  end.

(** Convert primitive to number (9.3) *)

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

(** Convert primitive to integer (9.4) *)

Definition convert_primitive_to_integer w :=
  convert_number_to_integer (convert_prim_to_number w).

(** Convert boolean to string *)

Definition convert_bool_to_string b :=
  if b then "true" else "false".

(** Convert primitive to string (9.8) *)

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
    (the code assumes [v1] and [v2] to both have type [ty].) 
    (11.9.3) *)

Definition equality_test_for_same_type ty v1 v2 :=
  match ty with
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

(** Strict equality comparison (11.9.6) *)

Definition strict_equality_test v1 v2 :=
  let ty1 := type_of v1 in
  let ty2 := type_of v2 in
  ifb ty1 = ty2
    then equality_test_for_same_type ty1 v1 v2
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

(** Inequality comparison for strings *)

Fixpoint inequality_test_string s1 s2 : bool :=
  match s1, s2 with
  | _, EmptyString => false
  | EmptyString, String _ _ => true
  | String c1 s1', String c2 s2' =>
     ifb c1 = c2
       then inequality_test_string s1' s2'
       else decide (int_of_char c1 < int_of_char c2)
  end.

(** Inequality comparison (11.8.5) *)

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
  | unary_op_typeof
  | unary_op_delete => False
  | _ => ~ prepost_unary_op op
  end.

(**************************************************************)
(** ** Factorization of rules for binary operators *)

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
  (* Note: could use the alternative definition:
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
    describing an object with a Call method. (9.11) *)

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

(** [typeof] for a value (11.4.3) *)

Definition typeof_value S v :=
  match v with
  | value_prim w => typeof_prim w
  | value_object l => If is_callable S l then "function" else "object"
  end.


(**************************************************************)
(** ** Auxiliary definitions for reduction of [valueOf] for primitive  *)

(** [value_viewable_as_prim s S v w] is a generic definition that is
    used to implement [value_viewable_as_bool] and 
    [value_viewable_as_number], where [s] is the classname,
    [S] is the state, [v] the value and [w] the primitive value. 
    (See 15.6.4.3 and 15.7.4.4) *)

Inductive value_viewable_as : string -> state -> value -> prim -> Prop :=
  | value_viewable_as_prim : forall s S w,
      value_viewable_as s S w w
  | value_viewable_as_object : forall s S l w,
      object_class S l s ->
      object_prim_value S l w ->
      value_viewable_as s S l w.


(**************************************************************)
(** ** Auxiliary definition used by object initializers *)

(** Interpretation of a string as a property name (11.1.5) *)

Definition string_of_propname (pn : propname) : prop_name :=
  match pn with 
  | propname_identifier s => s
  | propname_string s => s
  | propname_number n => JsNumber.to_string n
  end.

(** Interpretation of a native error code as a string (15.11.7.9) *)

Definition string_of_native_error (ne : native_error) :=
  match ne with
  | native_error_eval => "EvalError"
  | native_error_range => "RangeError"
  | native_error_ref => "ReferenceError"
  | native_error_syntax => "SyntaxError"
  | native_error_type => "TypeError"
  end.


(**************************************************************)
(** ** Auxiliary definition used in the reduction of [eval] *)

(** [is_syntactic_eval e] characterizes direct calls to eval *)

Definition is_syntactic_eval e :=
  match e with
  | expr_literal (literal_string s) => decide (s = "eval")
  | _ => false
  end.

(** Axiomatized parsing relation for eval *)

(* TODO: There are actually two passes of parsing.  One that performs
    the parsing, and the other that adds the additionnal informations,
    such as [add_infos_prog].  The second part depends of the current
    strictness flag.  Those function shouldn't thus perform this second
    pass.  We thus have to change the semantics so that it take this into
    account. *)

Axiom parse : string -> option prog -> Prop.
Axiom parse_exists : forall s, exists oprog, parse s oprog.
Axiom parse_pickable : forall s, Pickable (parse s).


(**************************************************************)
(**************************************************************)
(**************************************************************)
(* LATER: for for loops

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

*)

