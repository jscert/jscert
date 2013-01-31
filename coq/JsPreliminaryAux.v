Set Implicit Arguments.
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
Implicit Type B : builtin.
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

Global Instance attributes_data_comparable : Comparable attributes_data.
Admitted. (* TODO *)


(**************************************************************)
(** ** Type [attributes_accessor] *)

Global Instance attributes_accessor_comparable : Comparable attributes_accessor.
Admitted. (* TODO *)


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
Proof. typeclass. Qed.

Global Instance env_record_binds_pickable : forall S L,
  Pickable (env_record_binds S L).
Proof. typeclass. Qed.


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

Global Instance res_label_in_dec : forall R labs,
  Decidable (res_label_in R labs).
Proof.
  introv. unfold res_label_in. destruct (res_label R).
   skip. (* TODO:  set manipulations *)
   typeclass.
Qed.

Global Instance prepost_unary_op_dec : forall op,
  Decidable (prepost_unary_op op).
Proof. introv. destruct op; typeclass. Qed.


