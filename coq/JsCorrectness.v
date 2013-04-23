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
(*Implicit Type B : builtin.*)
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


Ltac inverts_not_ter NT I :=
  let NT' := fresh NT in
  inversion NT as [NT'|NT'|NT']; clear NT; (* [inverts NT as NT'] does not work. *)
  symmetry in NT';
  try rewrite NT' in * |-;
  try inverts I.

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

(* Unfolds one monadic contructor in the environnement. *)
Ltac if_unmonad := (* This removes some information... *)
  let NT := fresh "NT" in
  let E := fresh "Eq" in
  let S := fresh "S" in
  let R := fresh "R" in
  match goal with

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

  end.


(**************************************************************)
(** Other Tactics *)

Ltac unfold_matches_in T :=
  match T with

  (* Some exceptions to avoid looping *)
  | arbitrary => fail 1
  | run_equal => fail 1

  | run_prog => auto
  | run_stat => auto
  | run_expr => auto
  | run_elements => auto
  | run_call_full => auto
  | run_call => auto

  | result_normal out_div => auto*
  | result_normal ?o =>
    first [ discriminate
          | let P := get_head o in unfold P
          | auto* ]
  | result_stuck => discriminate
  | result_bottom => discriminate

  | match ?res with
    | result_normal o => ?C1
    | result_stuck => ?C2
    | result_bottom => ?C3
    end =>
    asserts: (res <> result_normal out_div);
    [ idtac
    | let res0 := fresh "res" in
      sets_eq res0: res;
      destruct res0 ]

  | match ?o with
    | out_div => ?C1
    | out_ter s r => ?C2
    end =>
    let o0 := fresh "o" in
    sets_eq o0: o;
    destruct o0; tryfalse

  | match ?t with
    | restype_normal => ?C1
    | restype_break => ?C2
    | restype_continue => ?C3
    | restype_return => ?C4
    | restype_throw => ?C5
    end =>
    let t0 := fresh "t" in
    sets_eq t0: t;
    destruct t0

  | match ?rv with
    | resvalue_empty => ?C1
    | resvalue_value v => ?C2
    | resvalue_ref r => ?C3
    end =>
    let rv0 := fresh "rv" in
    sets_eq rv0: rv;
    destruct rv0

  | match ?rk with
    | ref_kind_null => ?C1
    | ref_kind_undef => ?C2
    | ref_kind_primitive_base => ?C3
    | ref_kind_object => ?C4
    | ref_kind_env_record => ?C5
    end =>
    let rk0 := fresh "rk" in
    sets_eq rk0: rk;
    destruct rk0

  | match ?v with
    | value_prim w => ?C1
    | value_object l => ?C2
    end =>
    let v0 := fresh "v" in
    sets_eq v0: v;
    destruct v0

  | match ?w with
    | prim_undef => ?C1
    | prim_null => ?C2
    | prim_bool b => ?C3
    | prim_number n => ?C4
    | prim_string s => ?C5
    end =>
    let w0 := fresh "w" in
    sets_eq w0: w;
    destruct w0

  | match ?op with
    | None => ?C1
    | Some s => ?C2
    end =>
    let op0 := fresh "op" in
    sets_eq op0: op;
    destruct op0

  | match ?D with
    | full_descriptor_undef => ?C1
    | full_descriptor_some A => ?C2
    end =>
    let D0 := fresh "D" in
    sets_eq D0: D;
    destruct D0

  | match ?A with
    | attributes_data_of Ad => ?C1
    | attributes_accessor_of Aa => ?C2
    end =>
    let A0 := fresh "A" in
    sets_eq A0: A;
    destruct A0

  | match ?E with
    | env_record_decl Ed => ?C1
    | env_record_object l b => ?C2
    end =>
    let E0 := fresh "E" in
    sets_eq E0: E;
    destruct E0

  | match ?t with
    | type_undef => ?C1
    | type_null => ?C2
    | type_bool => ?C3
    | type_number => ?C4
    | type_string => ?C5
    | type_object => ?C6
    end =>
    let t0 := fresh "t" in
    sets_eq t0: t;
    destruct t0

  | match ?B with
    | builtin_default_value_default => ?C
    end =>
    let B0 := fresh "B" in
    sets_eq B0: B;
    destruct B0

  | match ?B with
    | builtin_put_default => ?C
    end =>
    let B0 := fresh "B" in
    sets_eq B0: B;
    destruct B0

  | match ?B with
    | builtin_define_own_prop_default => ?C
    end =>
    let B0 := fresh "B" in
    sets_eq B0: B;
    destruct B0

  | match ?c with
    | call_default => ?C1
    | call_after_bind => ?C2
    | call_prealloc C => ?C3
    end =>
    let c0 := fresh "c" in
    sets_eq c0: c;
    destruct c0

  | match ?op with
    | unary_op_delete => ?C1
    | unary_op_void => ?C2
    | unary_op_typeof => ?C3
    | unary_op_post_incr => ?C4
    | unary_op_post_decr => ?C5
    | unary_op_pre_incr => ?C6
    | unary_op_pre_decr => ?C7
    | unary_op_add => ?C8
    | unary_op_neg => ?C9
    | unary_op_bitwise_not => ?C10
    | unary_op_not => ?C11
    end =>
    let op0 := fresh "op" in
    sets_eq op0: op;
    destruct op0

  | match ?op with
    | binary_op_mult => ?C1
    | binary_op_div => ?C2
    | binary_op_mod => ?C3
    | binary_op_add => ?C4
    | binary_op_sub => ?C5
    | binary_op_left_shift => ?C6
    | binary_op_right_shift => ?C7
    | binary_op_unsigned_right_shift => ?C8
    | binary_op_lt => ?C9
    | binary_op_gt => ?C10
    | binary_op_le => ?C11
    | binary_op_ge => ?C12
    | binary_op_instanceof => ?C13
    | binary_op_in => ?C14
    | binary_op_equal => ?C15
    | binary_op_disequal => ?C16
    | binary_op_strict_equal => ?C17
    | binary_op_strict_disequal => ?C18
    | binary_op_bitwise_and => ?C19
    | binary_op_bitwise_or => ?C20
    | binary_op_bitwise_xor => ?C21
    | binary_op_and => ?C22
    | binary_op_or => ?C23
    | binary_op_coma => ?C24
    end =>
    let op0 := fresh "op" in
    sets_eq op0: op;
    destruct op0

  | match ?rb with
    | ref_base_type_value v => ?C1
    | ref_base_type_env_loc L => ?C2
    end =>
    let rb0 := fresh "rb" in
    sets_eq rb0: rb;
    destruct rb0

  | let a := ?f in ?C =>
    first [unfold_matches_in f | destruct~ f]
  | let (a, b) := ?f in ?C =>
    first [unfold_matches_in f | destruct~ f]
  | let '(a, b) := ?f in ?C =>
    first [unfold_matches_in f | destruct~ f]

  | ?f ?x => unfold_matches_in f
  | ?f => unfolds f

  end.

Ltac prove_not_div_with k1 k2 :=
  repeat first
    [ k1
    | match goal with
      | H : result_normal out_div = ?f ?x
        |- (result_normal out_div) <> (result_normal out_div) =>
        asserts: (f x <> result_normal out_div);
        [ clear H | false~ ]
      | |- (if ?b then ?C1 else ?C2) <> (result_normal out_div) =>
        case_if
      | |- (ifb ?b then ?C1 else ?C2) <> (result_normal out_div) =>
        case_if
      | |- (result_normal (if ?b then ?C1 else ?C2)) <> (result_normal out_div) =>
        case_if
      | |- (result_normal (ifb ?b then ?C1 else ?C2)) <> (result_normal out_div) =>
        case_if
      | |- ?T <> (result_normal out_div) =>
        unfold_matches_in T
      end
    | k2].

Ltac prove_not_div :=
  prove_not_div_with ltac:fail ltac:(simpl; auto).

Ltac prove_not_div_using P :=
  prove_not_div_with ltac:(apply P) ltac:(simpl; auto).

Ltac prove_not_div_using2 P1 P2 :=
  prove_not_div_with ltac:(apply P1 || apply P2) ltac:(simpl; auto).


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

Lemma prim_new_object_not_div : forall S w,
  prim_new_object S w <> out_div.
Proof.
  introv. prove_not_div. skip. (* Needs implementation of [prim_new_object] *)
Qed.

Lemma ref_get_value_not_div : forall wrun_expr wrun_stat wrun_prog wrun_call wrun_call_full,
  (forall S C e, wrun_expr S C e <> result_normal out_div) ->
  (forall S C t, wrun_stat S C t <> result_normal out_div) ->
  (forall S C p, wrun_prog S C p <> result_normal out_div) ->
  (forall S C B args, wrun_call S C B args <> result_normal out_div) ->
  (forall S C l v args, wrun_call_full S C l v args <> result_normal out_div) ->
  forall S C rv,
    ref_get_value (make_runs
      wrun_expr wrun_stat wrun_prog wrun_call wrun_call_full)
      S C rv <> out_div.
Proof.
  introv IHe IHt IHp IHc IHcf. introv.
  prove_not_div.
  (* The reason why it stops there is that there is an instance of [decide] applied
   deep in the term that prevents from doing any useful deconstruction over the matched
   term.  Let's split this [decide] and see what we can then do. *)
  case_if; prove_not_div_using prim_new_object_not_div.
Qed.


(**************************************************************)
(** Correctness of interpreter *)

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


(**************************************************************)
(** Operations on environments *)


(**************************************************************)
(** ** Main theorems *)

Theorem run_prog_not_div : forall num S C p,
  run_prog num S C p <> out_div
with run_stat_not_div : forall num S C t,
  run_stat num S C t <> out_div
with run_expr_not_div : forall num S C e,
  run_expr num S C e <> out_div
with run_elements_not_div : forall num S C rv els,
  run_elements num S C rv els <> out_div
with run_call_not_div : forall num S C B args,
  run_call num S C B args <> out_div
with run_call_full_not_div : forall num S C l v args,
  run_call_full num S C l v args <> out_div.
Proof.

  (* run_prog_not_div *)
  destruct num. discriminate.
  introv. destruct p. simpls. auto*.

  (* run_stat_not_div *)
  destruct num. discriminate.
  introv. destruct t; simpls; prove_not_div_using ref_get_value_not_div.

  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)

  (* run_expr_not_div *)
  destruct num. discriminate.
  introv. destruct e; simpls; auto*; skip. (* destruct e; simpls; prove_not_div. *) (* This is taking much too long...  Maybe the tactics are a little too heavy there. *)

  (* run_elements_not_div *)
  destruct num. discriminate.
  introv. destruct els as [|[?|?]]; simpls; prove_not_div.

  (* run_call_not_div *)
  destruct num. discriminate.
  introv. destruct B; simpls; prove_not_div_using ref_get_value_not_div.

  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)
  skip. (* Needs implementation. *)

  (* run_call_full_not_div *)
  destruct num. discriminate.
  introv. simpls. prove_not_div.

  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Needs implementation. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)
  skip. (* Has to be proved in a separate lemma. *)

Admitted.


Theorem run_prog_correct : forall num,
  follow_prog (run_prog num)
with run_stat_correct : forall num,
  follow_stat (run_stat num)
with run_expr_correct : forall num,
  follow_expr (run_expr num)
with run_elements_correct : forall num rv,
  follow_elements rv (fun S C => run_elements num S C rv)
with run_call_correct : forall num vs,
  follow_call vs (fun S C B => run_call num S C B vs)
with run_call_full_correct : forall num l vs,
  follow_call_full l vs (fun S C v => run_call_full num S C l v vs).
Proof.

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

