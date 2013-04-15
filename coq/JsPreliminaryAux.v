Set Implicit Arguments.
Require Import Shared.
Require Export JsSyntax JsSyntaxAux JsPreliminary.

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
(** ** Auxilary instances to define some comparison operators *)

Global Instance if_some_then_same_dec : forall (A : Type) F (x y : option A),
  (forall u v : A, Decidable (F u v)) ->
  Decidable (if_some_then_same F x y).
Proof.
  introv D.
  destruct x; destruct y; simpls~; typeclass.
Qed.

Lemma if_some_value_then_same_self : forall vo,
  if_some_value_then_same vo vo.
Proof.
  introv. unfolds. unfolds. destruct~ vo. reflexivity.
Qed.

Lemma if_some_bool_then_same_self : forall bo,
  if_some_bool_then_same bo bo.
Proof.
  introv. destruct bo; simpls~.
Qed.


(**************************************************************)
(** ** Type [attributes_data] *)

(** Boolean comparison *)

Definition attributes_data_compare Ad1 Ad2 :=
  match Ad1, Ad2 with
  | attributes_data_intro v1 w1 e1 c1, attributes_data_intro v2 w2 e2 c2 =>
    decide (v1 = v2 /\ w1 = w2 /\ e1 = e2 /\ c1 = c2)
  end.

(** Decidable comparison *)

Global Instance attributes_data_comparable : Comparable attributes_data.
Proof.
  applys (comparable_beq attributes_data_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H;
    [lets~ (H1&H2&H3&H4): (rm H) | inverts~ H]; congruence.
  (* Note that this is not the usual proof, which didn't worked there. -- Martin. *)
Qed.


(**************************************************************)
(** ** Type [attributes_accessor] *)

(** Boolean comparison *)

Definition attributes_accessor_compare Aa1 Aa2 :=
  match Aa1, Aa2 with
  | attributes_accessor_intro v1 w1 e1 c1, attributes_accessor_intro v2 w2 e2 c2 =>
    decide (v1 = v2 /\ w1 = w2 /\ e1 = e2 /\ c1 = c2)
  end.

(** Decidable comparison *)

Global Instance attributes_accessor_comparable : Comparable attributes_accessor.
Proof.
  applys (comparable_beq attributes_accessor_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H;
    [lets~ (H1&H2&H3&H4): (rm H) | inverts~ H]; congruence.
  (* Note that this is not the usual proof, which didn't worked there. -- Martin. *)
Qed.


(**************************************************************)
(** ** Type [attributes] *)

(** Boolean comparison *)

Definition attributes_compare A1 A2 :=
  match A1, A2 with
  | attributes_data_of Ad1, attributes_data_of Ad2 => decide (Ad1 = Ad2)
  | attributes_accessor_of Aa1, attributes_accessor_of Aa2 => decide (Aa1 = Aa2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance attributes_comparable : Comparable attributes.
Proof.
  applys (comparable_beq attributes_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [full_descriptor] *)

(** Inhabitants **)

Global Instance full_descriptor_inhab : Inhab full_descriptor.
Proof. apply (prove_Inhab full_descriptor_undef). Qed.

(** Boolean comparison *)

Definition full_descriptor_compare An1 An2 :=
  match An1, An2 with
  | full_descriptor_undef, full_descriptor_undef => true
  | full_descriptor_some A1, full_descriptor_some A2 => decide (A1 = A2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance full_descriptor_comparable : Comparable full_descriptor.
Proof.
  applys (comparable_beq full_descriptor_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [ref_kind] *)

(** Inhabitants **)

Global Instance ref_kind_inhab : Inhab ref_kind.
Proof. apply (prove_Inhab ref_kind_null). Qed.

(** Decidable comparison *)

Global Instance ref_kind_comparable : Comparable ref_kind.
Proof.
  apply make_comparable. introv.
  destruct x; destruct y;
    ((rewrite~ prop_eq_True_back; apply true_dec) ||
      (rewrite~ prop_eq_False_back; [apply false_dec | discriminate])).
Qed.


(**************************************************************)
(** ** Some pickable instances *)

Global Instance object_binds_pickable : forall S l,
  Pickable (object_binds S l).
Proof.
  introv. applys pickable_make (Heap.read (state_object_heap S) l).
  unfolds object_binds. introv [a Ba]. erewrite~ @Heap.binds_equiv_read.
  erewrite~ @Heap.indom_equiv_binds. eexists. auto*.
Qed.

Global Instance env_record_binds_pickable : forall S L,
  Pickable (env_record_binds S L).
Proof.
  introv. applys pickable_make (Heap.read (state_env_record_heap S) L).
  unfolds env_record_binds. introv [a Ba]. erewrite~ @Heap.binds_equiv_read.
  erewrite~ @Heap.indom_equiv_binds. eexists. auto*.
Qed.

Global Instance decl_env_record_pickable : forall Ed x,
  Pickable (Heap.binds Ed x).
Proof.
  introv. (*destruct Ed.*) skip. (* TODO:  Why is that opaque?!?! *)
Qed.

(**************************************************************)
(** ** Some decidable instances *)

Global Instance descriptor_is_data_dec : forall Desc,
  Decidable (descriptor_is_data Desc).
Proof.
  introv. apply neg_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_accessor_dec : forall Desc,
  Decidable (descriptor_is_accessor Desc).
Proof.
  introv. apply neg_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_generic_dec : forall Desc,
  Decidable (descriptor_is_generic Desc).
Proof. typeclass. Qed.

Global Instance prepost_unary_op_dec : forall op,
  Decidable (prepost_unary_op op).
Proof. introv. destruct op; typeclass. Qed.

Global Instance attributes_is_data_dec : forall A,
  Decidable (attributes_is_data A).
Proof. intro A. destruct A; typeclass. Qed.


Definition run_object_heap_map_properties S l F : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_map_properties O F).

Global Instance object_heap_map_properties_pickable : forall S l F,
  Pickable (object_heap_map_properties S l F).
Proof.
  introv. applys pickable_make (run_object_heap_map_properties S l F).
  introv [a [O [B E]]]. exists O. splits~.
  unfolds run_object_heap_map_properties.
  fequals. fequals. forwards*: @pick_spec (object_binds S l).
  unfolds object_binds. erewrite @Heap.binds_equiv_read_option in B,H.
  rewrite H in B. inverts~ B.
Qed.

Global Instance object_set_property_pickable : forall S l x A,
  Pickable (object_set_property S l x A).
Proof. typeclass. Qed.

Global Instance descriptor_contains_dec : forall Desc1 Desc2,
  Decidable (descriptor_contains Desc1 Desc2).
Proof.
  intros Desc1 Desc2. destruct Desc1; destruct Desc2.
  simpl. repeat apply and_decidable; try typeclass.
Qed.

Global Instance descriptor_enumerable_not_same_dec : forall A Desc,
   Decidable (descriptor_enumerable_not_same A Desc).
Proof.
  introv. unfolds descriptor_enumerable_not_same.
  destruct (descriptor_enumerable Desc); try typeclass.
Qed.

Global Instance descriptor_value_not_same_dec : forall Ad Desc,
   Decidable (descriptor_value_not_same Ad Desc).
Proof.
  introv. unfolds descriptor_value_not_same.
  destruct (descriptor_value Desc); try typeclass.
Qed.

Global Instance descriptor_get_not_same_dec : forall Aa Desc,
   Decidable (descriptor_get_not_same Aa Desc).
Proof.
  introv. unfolds descriptor_get_not_same.
  destruct (descriptor_get Desc); try typeclass.
Qed.

Global Instance descriptor_set_not_same_dec : forall Aa Desc,
   Decidable (descriptor_set_not_same Aa Desc).
Proof.
  introv. unfolds descriptor_set_not_same.
  destruct (descriptor_set Desc); try typeclass.
Qed.

Global Instance attributes_change_enumerable_on_non_configurable_dec : forall A Desc,
  Decidable (attributes_change_enumerable_on_non_configurable A Desc).
Proof. introv. apply and_decidable; try typeclass. Qed.

Global Instance attributes_change_data_on_non_configurable_dec : forall Ad Desc,
  Decidable (attributes_change_data_on_non_configurable Ad Desc).
Proof. introv. repeat apply and_decidable; try typeclass. Qed.

Global Instance attributes_change_accessor_on_non_configurable_dec : forall Aa Desc,
  Decidable (attributes_change_accessor_on_non_configurable Aa Desc).
Proof. introv. typeclass. Qed.


(** Decidable instance for [is_callable] *)

Definition run_callable S v : option call :=
  match v with
  | value_prim w => None
  | value_object l => object_call_ (pick (object_binds S l))
  end.

Global Instance is_callable_dec : forall S v,
  Decidable (is_callable S v).
Proof.
  introv. applys decidable_make
    (morph_option false (fun _ => true) (run_callable S v)).
  skip. (* TODO:  This proof has already been done, but with the old version of heaps. *)
Qed.


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



