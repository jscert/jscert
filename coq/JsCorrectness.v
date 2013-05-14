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
(* TODO:  Remove this section once I'll be sure it's useless. *)

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


(*
(* [need_ter I NT E res S R] generates two goals:
   * one where [not_ter res]
   * one where [res = out_ter S R] *)
Ltac need_ter I NT E res S R k :=
  let res0 := fresh "res" in
  let EQres0 := fresh I in
  sets_eq res0 EQres0: res;
  symmetry in EQres0;
  tests NT: (not_ter res0); [
      try solve [ inverts_not_ter NT I ]
    | rewrite not_ter_forall in NT;
      lets (S&R&E): (rm NT); rewrite E in I; clear E; simpl in I; k ].
*)

(*
(* Unfolds one monadic contructor in the environnement, calling the
  continuation when getting a [not_ter]. *)
Ltac if_unmonad k :=
(*
  let NT := fresh "NT" in
  let E := fresh "Eq" in
  let S := fresh "S" in
  let R := fresh "R" in
*)
  match goal with

(*
  | I: if_success_value ?runs ?C ?rev ?K = ?res |- ?g =>
    unfold if_success_value in I; if_unmonad

  | I: if_success ?rev ?K = ?res |- ?g =>
    unfold if_success in I; if_unmonad

  | I: if_success_state ?rv ?res ?K = ?res' |- ?g =>
    need_ter I NT E res S R ltac:(
      let C := fresh "C" in
      asserts C: ((res_type R = restype_normal -> g)
        /\ (res_type R = restype_break -> g)
        /\ ((res_type R = restype_continue
          \/ res_type R = restype_return
          \/ res_type R = restype_throw) ->
        result_normal (out_ter S (res_overwrite_value_if_empty rv R))
          = res' -> g)); [
          splits;
          let RT := fresh "RT" in
          introv RT; first [ rewrite RT in I | clear I; introv I ]
      | let C1 := fresh "C" in
        let C2 := fresh "C" in
        let C3 := fresh "C" in
        lets (C1&C2&C3): (rm C);
        destruct (res_type R); [ apply C1 | apply C2
          | apply C3 | apply C3 | apply C3 ];
          first [ reflexivity | inverts~ I; fail | idtac] ])

  | I: if_ter ?res ?K = ?res' |- ?g =>
    need_ter I NT E res S R ltac:idtac

  | I: result_normal (out_ter ?S1 ?R1)
      = result_normal (out_ter ?S0 ?R0) |- ?g =>
    inverts~ I

  | I: out_ter ?S1 ?R1 = out_ter ?S0 ?R0 |- ?g =>
    inverts~ I
*)

  | I : if_bool_option_result ?op ?K1 ?K2 = out_ter ?S0 ?R0 =>
    

  end.
*)


(**************************************************************)
(** Correctness Properties *)

Definition follow_spec {T Te : Type}
    (conv : T -> Te) (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> result) := forall S C (e : T) o,
  run S C e = o ->
  red S C (conv e) o.

Definition follow_expr := follow_spec expr_basic red_expr.
Definition follow_stat := follow_spec stat_basic red_stat.
Definition follow_prog := follow_spec prog_basic red_prog.
Definition follow_elements rv :=
  follow_spec (prog_1 rv) red_prog.
Definition follow_call vs :=
  follow_spec
    (fun B => spec_call_prealloc B vs)
    red_expr.
Definition follow_call_full l vs :=
  follow_spec
    (fun v => spec_call l v vs)
    red_expr.


Record runs_type_correct runs (*run_elements*) :=
  make_runs_type_correct {
    runs_type_correct_expr : follow_expr (runs_type_expr runs);
    runs_type_correct_stat : follow_stat (runs_type_stat runs);
    runs_type_correct_prog : follow_prog (runs_type_prog runs)(*;
    runs_type_correct_elements : follow_elements run_elements;
    runs_type_correct_call : follow_call (runs_type_call runs);
    runs_type_correct_call_full : follow_call_full (runs_type_call_full runs)*)
  }.



(**************************************************************)
(** Operations on objects *)

(* TODO
Lemma run_object_method_correct :
  forall Proj S l,
  (* TODO:  Add correctness properties. *)
    object_method Proj S l (run_object_method Proj S l).
Proof.
  introv. eexists. splits*.
  apply pick_spec.
  skip. (* Need properties about [l]. *)
Qed.
*)


(**************************************************************)
(** Operations on environments *)


(**************************************************************)
(** ** Main theorems *)

Theorem runs_correct : forall num,
  runs_type_correct (runs num).
Proof.

  induction num.
   constructors; introv R; inverts R.

   lets [IHe IHs IHp]: (rm IHnum).
   constructors.

   (* run_expr *)
   skip.

   (* run_stat *)
   skip.

   (* run_prog *)
   skip.

Qed.

(*
  (* run_prog_correct *)
  destruct num. auto*.
  intros S0 C p o R. destruct p as [str es].
  forwards RC: run_elements_correct R.
  apply~ red_prog_prog.

  (* run_stat_correct *)
  destruct num. auto*.
  intros S0 C t o R. destruct t.

   (* stat_expr *)
   simpls. repeat if_unmonad.
    inverts_not_ter NT R. forwards: run_expr_correct R2.
     apply red_stat_abort. (* TODO:  This could be turned into a tactic. *)
      skip. (* Needs implementation of [out_of_ext_stat]. *)
      constructors.
      intro A. inverts A.
    inverts_not_ter NT R.
  (* forwards: run_expr_correct R2.
     apply red_stat_abort. (* TODO:  This could be turned into a tactic. *)
      skip. (* Needs implementation of [out_of_ext_stat]. *)
      constructors.
      intro A. inverts A.*)
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.

   (* stat_label *)
   skip.

   (* TODO: Complete *)
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.
   skip.

  (* run_expr_correct *)
  skip.

  (* run_elements_correct *)
  skip.

  (* run_call_correct *)
  skip.

  (* run_call_full_correct *)
  skip.

Admitted.
*)

