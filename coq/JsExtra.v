Set Implicit Arguments.
Require Import JsSemanticsAux.

(*--------------------------------------------------------------*)
(** * Demo for [indom_simpl] *)

Lemma indom_simpl_demo_1 : forall h l f f' v v',
   indom (write (write h l f' v') l f v) l f'.
Proof. intros. indom_simpl. Qed.

Lemma indom_simpl_demo_2 : forall h l l' f f' v',
  indom (write h l' f' v') l f.
Proof. intros. indom_simpl. Admitted.

Lemma indom_simpl_demo_3 : forall h l f l' fvs' v,
  indom (write_fields (write h l f v) l' fvs') l f.
Proof. intros. indom_simpl. Admitted.

(*--------------------------------------------------------------*)
(** * Demo for [binds_simpl_step] *)

Lemma binds_simpl_step_demo_1 : forall h l f v,
   binds (write h l f v) l f v.
Proof. intros. binds_simpl_step. Qed.

Lemma binds_simpl_step_demo_2 : forall h l l' f f' v v',
  f' <> f -> binds (write h l' f' v') l f v.
Proof. intros. binds_simpl_step. Admitted.

Lemma binds_simpl_step_demo_3 : forall h l f v l' fvs',
  l' <> l -> binds (write_fields h l' fvs') l f v.
Proof. intros. binds_simpl_step. Admitted.

(*--------------------------------------------------------------*)
(** * Demo for [binds_cases] *)

Lemma binds_cases_demo_1 : forall h l f v v',
  binds (write h l f v) l f v' -> True.
Proof. introv H. binds_cases H. Admitted.

Lemma binds_cases_demo_2 : forall h l l' f f' v v',
  f' <> f -> binds (write h l' f' v') l f v -> True.
Proof. introv N H. binds_cases H. Admitted.

Lemma binds_cases_demo_3 : forall h l l' f f' v v' v'',
  f' <> f -> binds (write (write h l f v'') l' f' v') l f v -> True.
Proof. introv N H. binds_cases H. Admitted.

Lemma binds_cases_demo_4 : forall h l f f' f'' v v' v'' l',
  f' <> f -> binds (write_fields h l' ((f',v')::(f'',v'')::nil)) l f v -> True.
Proof. introv N H. binds_cases H. skip. skip. Admitted.


(*--------------------------------------------------------------*)
(** * Demo for [basic_value] *)

Example undef_basic :
  basic_value value_undef.
Proof. apply basic_undef. Qed.

(*Example int_basic :
  basic_value (value_number (number_of_int 17)).
Proof.
  apply basic_number.
Qed.*)

Example null_basic :
  basic_value (value_loc loc_null).
Proof.
  apply basic_null.
Qed.


