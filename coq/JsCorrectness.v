Set Implicit Arguments.
Require Import Shared.
Require Import LibFix LibList.
Require Import JsSyntax JsSyntaxAux JsPreliminary JsPreliminaryAux.
Require Import JsInterpreter JsPrettyInterm JsPrettyRules.


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
Implicit Type B : builtin.
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.
Implicit Type ct : codetype.

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
(** Generic constructions *)

Lemma get_arg_correct : forall args vs,
  arguments_from args vs ->
  forall num,
    num < length vs ->
    get_arg num args = LibList.nth num vs.
Proof.
  introv A. induction~ A.
   introv I. false I. lets (I'&_): (rm I). inverts~ I'.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_nil.
    rewrite length_cons in I. nat_math.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_cons.
    rewrite length_cons in I. nat_math.
Qed.


(**************************************************************)
(** Monadic constructors *)

Inductive not_ter : result -> Prop :=
  | not_ter_div : not_ter out_div
  | not_ter_stuck : not_ter result_stuck
  | not_ter_bottom : not_ter result_bottom.

Lemma not_ter_forall : forall res,
  ~ not_ter res <-> exists S R, res = out_ter S R.
Proof.
  iff P.
   destruct res; try (false P; constructors).
    destruct o. false P; constructors. repeat eexists.
   lets (S&R&E): (rm P). intro A. substs. inverts A.
Qed.


(* [need_ter I NT E res S R] generates two goals:
   * one where [not_ter res]
   * one where [res = out_ter S R] *)
Ltac need_ter I NT E res S R :=
  tests NT: (not_ter res); [|
    rewrite not_ter_forall in NT;
     lets (S&R&E): (rm NT); rewrite E in I; clear E; simpl in I ].

(* Unfolds one monadic contructor in the environnement. *)
Ltac if_unmonad :=
  let NT := fresh "NT" in
  let E := fresh "Eq" in
  let S := fresh "S" in
  let R := fresh "R" in
  match goal with

  | I: if_success_state ?rv ?res ?K
      = result_normal (out_ter ?S0 ?R0) |- ?g =>
    need_ter I NT E res S R; [
       try (inverts NT; inverts I; fail)
      | let C1 := fresh "C" in
        let C2 := fresh "C" in
        let C3 := fresh "C" in
        cuts C1: (res_type R = restype_normal -> g); [
        cuts C2: (res_type R = restype_break -> g); [
        cuts C3: ((res_type R = restype_continue
            \/ res_type R = restype_return
            \/ res_type R = restype_throw) ->
          out_ter S (res_overwrite_value_if_empty rv R)
            = out_ter S0 R0 -> g); [
        destruct (res_type R); [ apply C1 | apply C2
          | apply C3 | apply C3 | apply C3 ];
          (reflexivity || (inverts~ I; fail) || idtac)
        | clear C1 C2] | clear C1] |];
          let RT := fresh "RT" in
          introv RT ; (rewrite RT in I || (clear I; introv I)) ]

  | I: if_ter ?res ?K
      = result_normal (out_ter ?S0 ?R0) |- ?g =>
    need_ter I NT E res S R; [
       try (inverts NT; inverts I; fail) |]

  end.

Parameter gT : Prop.

Lemma test : forall res res0 S0 R0,
  if_ter res (fun S R =>
    if_success_state resvalue_empty res0 (fun S' rv =>
      result_stuck))
  = out_ter S0 R0 -> gT.
Proof.
  introv I.

  if_unmonad.
  cuts P: (result -> Prop).
  cuts: (P res0).
  if_unmonad.

  skip.
  skip.

  Set Printing All. idtac.

Admitted.


(**************************************************************)
(** ** Main theorem *)

Theorem run_prog_correct : forall num S C p o,
  (* TODO:  Add correctness statements. *)
  run_prog num S C p = o ->
  red_prog S C p o

with run_stat_correct : forall num S C t o,
  run_stat num S C t = o ->
  red_stat S C t o

with run_expr_correct : forall num S C e o,
  run_expr num S C e = o ->
  red_expr S C e o.
Proof.
Admitted.


