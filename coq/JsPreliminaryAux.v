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
(** ** Auxilary instances to define some comparison operators *)

Global Instance if_some_then_same_dec : forall (A : Type) F (x y : option A),
  (forall u v : A, Decidable (F u v)) ->
  Decidable (if_some_then_same F x y).
Proof.
  introv D.
  destruct x; destruct y; simpls~; typeclass.
Qed.

Global Instance some_compare_dec : forall (A : Type) F (x y : option A),
  (forall u v : A, Decidable (F u v)) ->
  Decidable (some_compare F x y).
Proof.
  introv D.
  destruct x; destruct y; simpls~; typeclass.
Qed.

Global Instance value_same_dec : forall v1 v2,
  Decidable (value_same v1 v2).
Proof.
  introv. unfolds value_same.
  sets_eq T1 E1: (type_of v1). sets_eq T2 E2: (type_of v2).
  cases_if; try typeclass.
  destruct T1; try typeclass.
  repeat cases_if; try typeclass.
Qed.

Global Instance prop_attributes_contains_dec : forall oldpf newpf,
  Decidable (prop_attributes_contains oldpf newpf).
Proof.
  introv. destruct oldpf. destruct newpf. simpl.
  repeat apply and_decidable; typeclass.
Qed.

Lemma value_same_self : forall v,
  value_same v v.
Proof.
  introv. unfolds value_same. sets_eq T E: (type_of v).
  cases_if; tryfalse. destruct~ T.
  repeat cases_if~.
   skip. (* Where is the lemma stating that zero <> neg_zero in JsNumber? *)
   skip.
Qed.

Lemma if_some_value_then_same_self : forall vo,
  if_some_value_then_same vo vo.
Proof.
  introv. unfolds. unfolds. destruct~ vo.
   apply value_same_self.
Qed.

Lemma if_some_bool_then_same_self : forall bo,
  if_some_bool_then_same bo bo.
Proof.
  introv. destruct bo; simpls~.
Qed.

Lemma prop_attributes_contains_self : forall A,
  prop_attributes_contains A A.
Proof.
  introv. destruct A. simpl.
  splits; (apply if_some_value_then_same_self
    || apply if_some_bool_then_same_self).
Qed.


(**************************************************************)
(** ** Type [prop_attributes] *)

(** Boolean comparison *)

Definition prop_attributes_compare A1 A2 :=
  decide (prop_attributes_contains A1 A2 /\ prop_attributes_contains A2 A1).

(** Decidable comparison *)

Global Instance prop_attributes_comparable : Comparable prop_attributes.
Proof.
  applys (comparable_beq prop_attributes_compare). intros x y.
  skip. (* TODO:  The magical tactic here does not work as it requires to destruct all option types in the context before doing all those congruence stuff. *)
Qed.


(**************************************************************)
(** ** Type [prop_descriptor] *)

(** Inhabitants **)

Global Instance prop_descriptor_inhab : Inhab prop_descriptor.
Proof. apply (prove_Inhab prop_descriptor_undef). Qed.

(** Boolean comparison *)

Definition prop_descriptor_compare An1 An2 :=
  match An1, An2 with
  | prop_descriptor_undef, prop_descriptor_undef => true
  | prop_descriptor_some A1, prop_descriptor_some A2 => decide (A1 = A2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance prop_descriptor_comparable : Comparable prop_descriptor.
Proof.
  applys (comparable_beq prop_descriptor_compare). intros x y.
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

