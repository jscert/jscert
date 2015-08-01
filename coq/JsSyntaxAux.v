Set Implicit Arguments.
Require Import LibLogic LibHeap.
Require Export JsSyntax.

Implicit Type l : object_loc.
Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type R : res.
Implicit Type Desc : descriptor.


(**************************************************************)
(** ** Smart constructors for objects *)

(** Builds an object with all optional fields to None *)

Definition object_create vproto sclass bextens P :=
  {| object_proto_ := vproto;
     object_class_ := sclass;
     object_extensible_ := bextens;
     object_properties_ := P;
     object_prim_value_ := None;
     object_get_ := builtin_get_default;
     object_get_own_prop_ := builtin_get_own_prop_default;
     object_get_prop_ := builtin_get_prop_default;
     object_put_ := builtin_put_default;
     object_can_put_ := builtin_can_put_default;
     object_has_prop_ := builtin_has_prop_default;
     object_delete_ := builtin_delete_default;
     object_default_value_ := builtin_default_value_default;
     object_define_own_prop_ := builtin_define_own_prop_default;
     object_construct_ := None;
     object_call_ := None;
     object_has_instance_ := None;
     object_scope_ := None;
     object_formal_parameters_ := None;
     object_code_ := None;
     object_target_function_ := None;
     object_bound_this_ := None;
     object_bound_args_ := None;
     object_parameter_map_ := None |}.

(** Sets proto field of an object. *)

Definition object_set_proto O v :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro v x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Sets class field of an object. *)

Definition object_set_class O s :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1  s x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Sets extensible to false to an object. *)

Definition object_set_extensible O b :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 b x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the primitive value field of an object *)

Definition object_with_primitive_value O v :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 (Some v) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the extensible field of an object *)

Definition object_with_extension O b :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 b x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the property field of an object. *)

Definition object_with_properties O properties :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 properties x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the non-optional operations on an object *)

Definition object_with_operations O g go gp p cp hp d dv do :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 g go gp p cp hp d dv do x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.
  
(** Modifies the get field of an object *)

Definition object_with_get O g :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 g x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the get_own_property field of an object *)

Definition object_with_get_own_property O gop :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 gop x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the construct, call and has_instance fields of an object *)

Definition object_with_invokation O constr call has_instance :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 constr call has_instance x18 x19 x20 x21 x22 x23 x24
  end.

(** Modifies the scope of an object *)

Definition object_with_scope O scope :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 scope x19 x20 x21 x22 x23 x24
  end.

(** Modifies the formal parameters of an object *)

Definition object_with_formal_params O params :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 params x20 x21 x22 x23 x24
  end.

(** Modifies the other parameters of an object *)

Definition object_with_details O scope params code target boundthis boundargs paramsmap :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 scope params code target boundthis boundargs paramsmap
  end.

(** Modifies the parameters for new Arrays *)

Definition object_for_array O defineownproperty :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 defineownproperty x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  end.
  
(** Modifies the parameters for the Arguments Object *)

Definition object_for_args_object O paramsmap get getownproperty defineownproperty delete :=
  match O with
  | object_intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 =>
    object_intro x1 x2 x3 x4 x5 get getownproperty x8 x9 x10 x11 delete x13 defineownproperty x15 x16 x17 x18 x19 x20 x21 x22 x23 (Some paramsmap)
  end.

(**************************************************************)
(** ** Type [builtin] *)

(** mathop *)

Global Instance mathop_inhab : Inhab mathop.
Proof. apply (prove_Inhab mathop_abs). Qed.

Definition mathop_compare m1 m2 :=
  match m1, m2 with
  | mathop_abs, mathop_abs => true
  end.

Global Instance mathop_comparable : Comparable mathop.
Proof.
  applys (comparable_beq mathop_compare). introv.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

(** native_error *)

Global Instance native_error_inhab : Inhab native_error.
Proof. apply (prove_Inhab native_error_eval). Qed.

Definition native_error_compare ne1 ne2 :=
  match ne1, ne2 with
  | native_error_eval, native_error_eval => true
  | native_error_range, native_error_range => true
  | native_error_ref, native_error_ref => true
  | native_error_syntax, native_error_syntax => true
  | native_error_type, native_error_type => true
  | native_error_uri, native_error_uri => true
  | _, _ => false
  end.

Global Instance native_error_comparable : Comparable native_error.
Proof.
  applys (comparable_beq native_error_compare). introv.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(** prealloc *)

Global Instance prealloc_inhab : Inhab prealloc.
Proof. apply (prove_Inhab prealloc_global). Qed.

  (* LATER: use a plugin to generate definitions *)

Definition prealloc_compare bl1 bl2 :=
  match bl1, bl2 with
  | prealloc_global, prealloc_global => true
  | prealloc_global_eval, prealloc_global_eval => true
  | prealloc_global_parse_int, prealloc_global_parse_int => true
  | prealloc_global_parse_float, prealloc_global_parse_float => true
  | prealloc_global_is_finite, prealloc_global_is_finite => true
  | prealloc_global_is_nan, prealloc_global_is_nan => true
  | prealloc_global_decode_uri, prealloc_global_decode_uri => true
  | prealloc_global_decode_uri_component, prealloc_global_decode_uri_component => true
  | prealloc_global_encode_uri, prealloc_global_encode_uri => true
  | prealloc_global_encode_uri_component, prealloc_global_encode_uri_component => true
  | prealloc_object, prealloc_object => true
  | prealloc_object_get_proto_of, prealloc_object_get_proto_of => true
  | prealloc_object_get_own_prop_descriptor , prealloc_object_get_own_prop_descriptor  => true
  | prealloc_object_get_own_prop_name, prealloc_object_get_own_prop_name => true
  | prealloc_object_create, prealloc_object_create => true
  | prealloc_object_define_prop, prealloc_object_define_prop => true
  | prealloc_object_define_props, prealloc_object_define_props => true
  | prealloc_object_seal, prealloc_object_seal => true
  | prealloc_object_freeze, prealloc_object_freeze => true
  | prealloc_object_prevent_extensions, prealloc_object_prevent_extensions => true
  | prealloc_object_is_sealed, prealloc_object_is_sealed => true
  | prealloc_object_is_frozen, prealloc_object_is_frozen => true
  | prealloc_object_is_extensible, prealloc_object_is_extensible => true
  | prealloc_object_keys, prealloc_object_keys => true
  | prealloc_object_keys_call, prealloc_object_keys_call => true
  | prealloc_object_proto, prealloc_object_proto => true
  | prealloc_object_proto_to_string, prealloc_object_proto_to_string => true
  | prealloc_object_proto_value_of, prealloc_object_proto_value_of => true
  | prealloc_object_proto_has_own_prop, prealloc_object_proto_has_own_prop => true
  | prealloc_object_proto_is_prototype_of, prealloc_object_proto_is_prototype_of => true
  | prealloc_object_proto_prop_is_enumerable, prealloc_object_proto_prop_is_enumerable => true
  | prealloc_function, prealloc_function => true
  | prealloc_function_proto, prealloc_function_proto => true
  | prealloc_function_proto_to_string, prealloc_function_proto_to_string => true
  | prealloc_function_proto_apply, prealloc_function_proto_apply => true
  | prealloc_function_proto_call, prealloc_function_proto_call => true
  | prealloc_function_proto_bind, prealloc_function_proto_bind => true
  | prealloc_bool, prealloc_bool => true
  | prealloc_bool_proto, prealloc_bool_proto => true
  | prealloc_bool_proto_to_string, prealloc_bool_proto_to_string => true
  | prealloc_bool_proto_value_of, prealloc_bool_proto_value_of => true
  | prealloc_number, prealloc_number => true
  | prealloc_number_proto, prealloc_number_proto => true
  | prealloc_number_proto_to_string, prealloc_number_proto_to_string => true
  | prealloc_number_proto_value_of, prealloc_number_proto_value_of => true
  | prealloc_number_proto_to_fixed, prealloc_number_proto_to_fixed => true
  | prealloc_number_proto_to_exponential, prealloc_number_proto_to_exponential => true
  | prealloc_number_proto_to_precision, prealloc_number_proto_to_precision => true
  | prealloc_array, prealloc_array => true
  | prealloc_array_is_array, prealloc_array_is_array => true
  | prealloc_array_proto, prealloc_array_proto => true
  | prealloc_array_proto_pop, prealloc_array_proto_pop => true
  | prealloc_array_proto_push, prealloc_array_proto_push => true
  | prealloc_array_proto_to_string, prealloc_array_proto_to_string => true
  | prealloc_array_proto_join, prealloc_array_proto_join => true
  | prealloc_string, prealloc_string => true
  | prealloc_string_proto, prealloc_string_proto => true
  | prealloc_string_proto_to_string, prealloc_string_proto_to_string => true
  | prealloc_string_proto_value_of, prealloc_string_proto_value_of => true
  | prealloc_string_proto_char_at, prealloc_string_proto_char_at => true
  | prealloc_string_proto_char_code_at, prealloc_string_proto_char_code_at => true
  | prealloc_math, prealloc_math => true
  | prealloc_mathop m1, prealloc_mathop m2 => decide (m1 = m2)
  | prealloc_date, prealloc_date => true
  | prealloc_regexp, prealloc_regexp => true
  | prealloc_error, prealloc_error => true
  | prealloc_error_proto, prealloc_error_proto => true
  | prealloc_native_error ne1, prealloc_native_error ne2 => decide (ne1 = ne2)
  | prealloc_native_error_proto ne1, prealloc_native_error_proto ne2 => decide (ne1 = ne2)
  | prealloc_error_proto_to_string, prealloc_error_proto_to_string => true
  | prealloc_throw_type_error, prealloc_throw_type_error => true
  | prealloc_json, prealloc_json => true
  | _,_ => false
  end.

Global Instance prealloc_comparable : Comparable prealloc.
Proof.
  applys (comparable_beq prealloc_compare). intros x y.
  (* This shall take a long, like some tens of seconds. *)
  destruct x; destruct y; simpls; iff; tryfalse; auto~; rew_refl in *; congruence.
Qed.


(**************************************************************)
(** ** Type [object_loc] *)

(** Inhabitant *)

Global Instance object_loc_inhab : Inhab object_loc.
Proof. apply (prove_Inhab (object_loc_normal 0%nat)). Qed.

(** Boolean comparison *)

Definition object_loc_compare l1 l2 :=
  match l1, l2 with
  | object_loc_normal ln1, object_loc_normal ln2 => decide (ln1 = ln2)
  | object_loc_prealloc bl1, object_loc_prealloc bl2 => decide (bl1 = bl2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance object_loc_comparable : Comparable object_loc.
Proof.
  applys (comparable_beq object_loc_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [prim] *)

(** Inhabitant *)

Global Instance prim_inhab : Inhab prim.
Proof. apply (prove_Inhab prim_undef). Qed.

(** Boolean comparison *)

Definition prim_compare w1 w2 :=
  match w1, w2 with
  | prim_undef, prim_undef => true
  | prim_null, prim_null => true
  | prim_bool b1, prim_bool b2 => decide (b1 = b2)
  | prim_number n1, prim_number n2 => decide (n1 = n2)
  | prim_string s1, prim_string s2 => decide (s1 = s2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance prim_comparable : Comparable prim.
Proof.
  applys (comparable_beq prim_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [value] *)

(** Inhabitant *)

Global Instance value_inhab : Inhab value.
Proof. applys prove_Inhab value_prim. typeclass. Qed.

(** Boolean comparison *)

Definition value_compare v1 v2 :=
  match v1, v2 with
  | value_prim w1, value_prim w2 => decide (w1 = w2)
  | value_object l1, value_object l2 => decide (l1 = l2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance value_comparable : Comparable value.
Proof.
  applys (comparable_beq value_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

(**************************************************************)
(** ** Type [mutability] *)

(** Inhabitant *)

Global Instance mutability_inhab : Inhab mutability.
Proof. apply (prove_Inhab mutability_deletable). Qed.

(** Boolean comparison *)

Definition mutability_compare m1 m2 : bool :=
  match m1, m2 with
  | mutability_uninitialized_immutable, mutability_uninitialized_immutable => true
  | mutability_immutable, mutability_immutable => true
  | mutability_nondeletable, mutability_nondeletable => true
  | mutability_deletable, mutability_deletable => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance mutability_comparable : Comparable mutability.
Proof.
  (* NOTE: this proof script could be improved to follow the pattern of similar proofs above *)
  apply make_comparable. introv.
  applys decidable_make (mutability_compare x y).
  destruct x; destruct y; simpl; rew_refl;
    ((rewrite~ eqb_eq; fail) || (rewrite~ eqb_neq; discriminate)).
Qed.


(**************************************************************)
(** ** Type [ref] *)

Global Instance ref_inhab : Inhab ref.
Proof.
  apply (prove_Inhab
           (ref_intro
                (ref_base_type_value (value_prim prim_undef))
                EmptyString
                false)).
Qed.

Definition ref_base_type_compare rb1 rb2 : bool :=
  match rb1, rb2 with
  | ref_base_type_value v1, ref_base_type_value v2 => decide (v1 = v2)
  | ref_base_type_env_loc l1, ref_base_type_env_loc l2 => decide (l1 = l2)
  | _, _ => false
  end.

Global Instance ref_base_type_comparable : Comparable ref_base_type.
Proof.
  apply (comparable_beq ref_base_type_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

Definition ref_compare r1 r2 : bool :=
  decide (ref_base r1 = ref_base r2 /\
          ref_name r1 = ref_name r2 /\
          ref_strict r1 = ref_strict r2).

Global Instance ref_comparable : Comparable ref.
Proof.
  apply (comparable_beq ref_compare). intros x y.
  destruct x.
  destruct y.
  unfolds ref_compare.
  simpl.
  rew_refl.
  iff.
  destruct H as [H1 [H2 H3]]. substs~.
  inverts~ H.
Qed.

(**************************************************************)
(** ** Type [env_record] *)

(** Inhabitants **)

Global Instance env_record_inhab : Inhab env_record.
Proof. apply (prove_Inhab (env_record_decl Heap.empty)). Qed.


(**************************************************************)
(** ** Type [state] *)

(** Inhabitants **)

Global Instance state_inhab : Inhab state.
Proof.
  apply (prove_Inhab
           (state_intro
              Heap.empty
              Heap.empty
              (LibStream.const 0)
              nil
           )
        ).
Qed.

(**************************************************************)
(** ** Type [type] *)

(** Inhabitants **)

Global Instance type_inhab : Inhab type.
Proof. applys prove_Inhab type_undef. Qed.

(** Boolean comparison *)

Definition type_compare t1 t2 :=
  match t1, t2 with
  | type_undef, type_undef => true
  | type_null, type_null => true
  | type_bool, type_bool => true
  | type_number, type_number => true
  | type_string, type_string => true
  | type_object, type_object => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance type_comparable : Comparable type.
Proof.
  applys (comparable_beq type_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.

(**************************************************************)
(** ** Type [object_properties_type] *)

(** Inhabitants **)

Global Instance object_properties_type_inhab : Inhab object_properties_type.
Proof. applys prove_Inhab @Heap.empty. Qed.


(**************************************************************)
(** ** Type [object] *)

(** Inhabitants **)

Global Instance object_inhab : Inhab object.
Proof. applys prove_Inhab object_create; try typeclass; try apply arbitrary. Qed.


(**************************************************************)
(** ** Type [res] *)

(** Inhabitants **)

Global Instance res_inhab : Inhab res.
Proof. apply (prove_Inhab res_empty). Qed.

(** Modification of fields *)

Definition res_with_type R rt : res :=
  match R with res_intro old_rt rv labopt => res_intro rt rv labopt end.

Definition res_with_value R rv : res :=
  match R with res_intro rt old_rv labopt => res_intro rt rv labopt end.


(**************************************************************)
(** ** Type [resvalue] *)

(** Inhabitants **)

Global Instance resvalue_inhab : Inhab resvalue.
Proof. apply (prove_Inhab resvalue_empty). Qed.

(** Boolean comparison *)

Definition resvalue_compare rv1 rv2 :=
  match rv1, rv2 with
  | resvalue_empty, resvalue_empty => true
  | resvalue_value v1, resvalue_value v2 =>
    decide (v1 = v2)
  | resvalue_ref r1, resvalue_ref r2 =>
    decide (r1 = r2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance resvalue_comparable : Comparable resvalue.
Proof.
  applys (comparable_beq resvalue_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [execution_ctx] *)

(** Update the strictness flag of an execution context *)

Definition execution_ctx_with_strict C bstrict :=
  match C with execution_ctx_intro le ve th bstrict_old =>
               execution_ctx_intro le ve th bstrict end.

(**************************************************************)
(** ** Type [literal] *)

(** Inhabitants **)

Global Instance literal_inhab : Inhab literal.
Proof. apply (prove_Inhab literal_null). Qed.

(** Boolean comparison *)

Fixpoint literal_compare i1 i2 :=
  match i1, i2 with
  | literal_null, literal_null => true
  | literal_bool b1, literal_bool b2 => decide (b1 = b2)
  | literal_number n1, literal_number n2 => decide (n1 = n2)
  | literal_string s1, literal_string s2 => decide (s1 = s2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance literal_comparable : Comparable literal.
Proof.
  applys (comparable_beq literal_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [unary_op] *)

(** Inhabitants **)

Global Instance unary_op_inhab : Inhab unary_op.
Proof. apply (prove_Inhab unary_op_void). Qed.

(** Boolean comparison *)

Fixpoint unary_op_compare op1 op2 :=
  match op1, op2 with
  | unary_op_delete, unary_op_delete => true
  | unary_op_void, unary_op_void => true
  | unary_op_typeof, unary_op_typeof => true
  | unary_op_post_incr, unary_op_post_incr => true
  | unary_op_post_decr, unary_op_post_decr => true
  | unary_op_pre_incr, unary_op_pre_incr => true
  | unary_op_pre_decr, unary_op_pre_decr => true
  | unary_op_add, unary_op_add => true
  | unary_op_neg, unary_op_neg => true
  | unary_op_bitwise_not, unary_op_bitwise_not => true
  | unary_op_not, unary_op_not => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance unary_op_comparable : Comparable unary_op.
Proof.
  applys (comparable_beq unary_op_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [binary_op] *)

(** Inhabitants **)

Global Instance binary_op_inhab : Inhab binary_op.
Proof. apply (prove_Inhab binary_op_coma). Qed.

(** Boolean comparison *)

Fixpoint binary_op_compare op1 op2 :=
  match op1, op2 with
  | binary_op_mult, binary_op_mult => true
  | binary_op_div, binary_op_div => true
  | binary_op_mod, binary_op_mod => true
  | binary_op_add, binary_op_add => true
  | binary_op_sub, binary_op_sub => true
  | binary_op_left_shift, binary_op_left_shift => true
  | binary_op_right_shift, binary_op_right_shift => true
  | binary_op_unsigned_right_shift, binary_op_unsigned_right_shift => true
  | binary_op_lt, binary_op_lt => true
  | binary_op_gt, binary_op_gt => true
  | binary_op_le, binary_op_le => true
  | binary_op_ge, binary_op_ge => true
  | binary_op_instanceof, binary_op_instanceof => true
  | binary_op_in, binary_op_in => true
  | binary_op_equal, binary_op_equal => true
  | binary_op_disequal, binary_op_disequal => true
  | binary_op_strict_equal, binary_op_strict_equal => true
  | binary_op_strict_disequal, binary_op_strict_disequal => true
  | binary_op_bitwise_and, binary_op_bitwise_and => true
  | binary_op_bitwise_or, binary_op_bitwise_or => true
  | binary_op_bitwise_xor, binary_op_bitwise_xor => true
  | binary_op_and, binary_op_and => true
  | binary_op_or, binary_op_or => true
  | binary_op_coma, binary_op_coma => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance binary_op_comparable : Comparable binary_op.
Proof.
  applys (comparable_beq binary_op_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [expr] *)

(** Inhabitants **)

Global Instance expr_inhab : Inhab expr.
Proof. apply (prove_Inhab expr_this). Qed.


(**************************************************************)
(** ** Type [stat] *)

(** Inhabitants **)

Global Instance stat_inhab : Inhab stat.
Proof. apply (prove_Inhab (stat_expr arbitrary)). Qed.


(**************************************************************)
(** ** Type [prog] *)

(** Inhabitants **)

Global Instance prog_inhab : Inhab prog.
Proof. apply (prove_Inhab (prog_intro true nil)). Qed.

(** Projections **)

Definition prog_intro_strictness p :=
  match p with prog_intro str els => str end.

Definition prog_elements p :=
  match p with prog_intro str els => els end.

(** Emptiness test *)

Definition prog_empty (p : prog) :=
  prog_elements p = nil.


(**************************************************************)
(** ** Type [funcbody] *)

(** Inhabitants **)

Global Instance body_inhab : Inhab funcbody.
Proof. apply prove_Inhab. apply (funcbody_intro arbitrary arbitrary). Qed.

(** Projections **)

Definition funcbody_prog fb :=
  match fb with
  | funcbody_intro p _ => p
  end.

Definition funcbody_string fb :=
  match fb with
  | funcbody_intro _ s => s
  end.

Definition funcbody_is_strict fb := 
  match fb with funcbody_intro (prog_intro b_strict _) _ => b_strict end.

(** Emptiness test *)

Definition funcbody_empty (bd : funcbody) :=
  prog_empty (funcbody_prog bd).


(**************************************************************)
(** ** Type [restype] *)

(** Inhabitants **)

Global Instance restype_inhab : Inhab restype.
Proof. apply (prove_Inhab restype_normal). Qed.

(** Boolean comparison *)

Definition restype_compare rt1 rt2 :=
  match rt1, rt2 with
  | restype_normal, restype_normal => true
  | restype_break, restype_break => true
  | restype_continue, restype_continue => true
  | restype_return, restype_return => true
  | restype_throw, restype_throw => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance restype_comparable : Comparable restype.
Proof.
  applys (comparable_beq restype_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [label] *)

(** Inhabitants **)

Global Instance label_inhab : Inhab label.
Proof. apply (prove_Inhab label_empty). Qed.

(** Boolean comparison *)

Definition label_compare lab1 lab2 :=
  match lab1, lab2 with
  | label_empty, label_empty => true
  | label_string s1, label_string s2 => decide (s1 = s2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance label_comparable : Comparable label.
Proof.
  applys (comparable_beq label_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [label_set] *)

Definition label_set_empty : label_set := nil.

Definition label_set_add lab labs := lab :: labs.

Definition label_set_add_empty labs := label_set_add label_empty labs.

Definition label_set_mem lab labs := decide (Mem lab labs).


(**************************************************************)
(** ** Type [attributes_data] *)

(** Inhabitant *)

Global Instance attribute_data_inhab : Inhab attributes_data.
Proof. apply* prove_Inhab. constructor; try typeclass. exact undef. Qed.

(** Modifies the writable field of a data attribute *)

Definition attributes_data_with_writable Ad bw' :=
  match Ad with attributes_data_intro v bw be bc =>
                attributes_data_intro v bw' be bc end.

(** Modifies the configurable field of a data attribute *)

Definition attributes_data_with_configurable Ad bc' :=
  match Ad with attributes_data_intro v bw be bc =>
                attributes_data_intro v bw be bc' end.
 
(** Modifies the value field of a data attribute *) 
                
Definition attributes_data_with_value Ad v' :=
  match Ad with attributes_data_intro v bw be bc =>
                attributes_data_intro v' bw be bc end.


(**************************************************************)
(** ** Type [descriptor] *)

(** Modifies the value field of a descriptor *)

Definition descriptor_with_value Desc v' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v' bw vg vs be bc end.

(** Modifies the writable field of a descriptor *)

Definition descriptor_with_writable Desc bw' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v bw' vg vs be bc end.

(** Modifies the get field of a descriptor *)

Definition descriptor_with_get Desc vg' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v bw vg' vs be bc end.

(** Modifies the set field of a descriptor *)

Definition descriptor_with_set Desc vs' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v bw vg vs' be bc end.

(** Modifies the enumerable field of a descriptor *)

Definition descriptor_with_enumerable Desc be' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v bw vg vs be' bc end.

(** Modifies the configurable field of a descriptor *)

Definition descriptor_with_configurable Desc bc' :=
  match Desc with descriptor_intro v bw vg vs be bc =>
                descriptor_intro v bw vg vs be bc' end.


(**************************************************************)
(** ** Type [attributes_accessor] *)

(** Inhabitant *)

Global Instance attribute_accessor_inhab : Inhab attributes_accessor.
Proof. apply* prove_Inhab. constructor; try typeclass; exact undef. Qed.

(** Modifies the configurable field of an accessor attribute *)

Definition attributes_acccessor_with_configurable Aa bc' :=
  match Aa with attributes_accessor_intro vg vs be bc =>
                attributes_accessor_intro vg vs be bc' end.


(**************************************************************)
(** ** Type [codetype] *)

(** Boolean comparison *)

Definition codetype_compare ct1 ct2 :=
  match ct1, ct2 with
  | codetype_func, codetype_func => true
  | codetype_global, codetype_global => true
  | codetype_eval, codetype_eval => true
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance codetype_comparable : Comparable codetype.
Proof.
  applys (comparable_beq codetype_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** LATER: complete this file with the missing types. *)

