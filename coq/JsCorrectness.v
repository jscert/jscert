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
(** Correctness Properties *)

Definition follow_spec {T Te : Type}
    (conv : T -> Te) (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> result) := forall S C (e : T) S' res,
  run S C e = out_ter S' res ->
  red S C (conv e) (out_ter S' res).

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


Record runs_type_correct runs run_elements :=
  make_runs_type_correct {
    runs_type_correct_expr : follow_expr (runs_type_expr runs);
    runs_type_correct_stat : follow_stat (runs_type_stat runs);
    runs_type_correct_prog : follow_prog (runs_type_prog runs);
    runs_type_correct_elements : forall rv,
      follow_elements rv (fun S C => run_elements S C rv);
    runs_type_correct_call : forall vs,
      follow_call vs (fun S C B => runs_type_call runs S C B vs);
    runs_type_correct_call_full : forall l vs,
      follow_call_full l vs (fun S C vthis => runs_type_call_full runs S C l vthis vs)
  }.


(**************************************************************)
(** Useful Tactics *)

Ltac absurd_neg :=
  let H := fresh in
  introv H; inverts H; tryfalse.

Ltac findHyp t :=
  match goal with
  | H : appcontext [ t ] |- _ => H
  | _ => fail "Unable to find an hypothesis for " t
  end.


(**************************************************************)
(** Monadic constructors *)

(* Unfolds one monadic contructor in the environnement, calling the
  continuation when getting an unsolved non-terminating reduction. *)
Ltac if_unmonad k :=
  match goal with

  | I : result_out (out_ter ?S1 ?R1) = result_out (out_ter ?S0 ?R0) |- ?g =>
    inverts~ I

  | I : if_ter ?o ?K = ?o0 |- ?g =>
    unfold if_ter in I;
    let o' := fresh "o" in
    let o'' := fresh "o" in
    let Eqo' := fresh "Eq" o' in
    sets_eq <- o' Eqo': o;
    destruct o' as [o''| |]; cbv beta in I;
      [destruct o'';
        [k I|]
      | k I | k I]

  | I : if_success_state ?rv ?o ?K = ?o0 |- ?g =>
    unfold if_success_state in I;
    if_unmonad k; (* Deal with the [if_ter]. *)
    match goal with
      I : match res_type ?r with
          | restype_normal => ?C1
          | restype_break => ?C2
          | restype_continue => ?C3
          | restype_return => ?C4
          | restype_throw => ?C5
          end = ?o0,
      I' : _ = result_out (out_ter ?s ?r) |- _ =>
      let rt := fresh "rt" in
      sets_eq <- rt: (res_type r);
      let T1 := fresh "T" in
      tests_basic T1: (rt = restype_normal);
        [ rewrite T1 in * |- *; clear T1
        | let T2 := fresh "T" in
          tests_basic T2: (rt = restype_throw);
            [ rewrite T2 in I
            | let I'' := fresh "R" in
              asserts I'': (C2 = o0);
                [ destruct rt; tryfalse; auto*
                | clear I; rename I'' into I]]]
    end

  | I : if_success ?o ?K = ?o0 |- ?g =>
    unfold if_success in I

  | I : if_not_throw ?rv ?o ?K = ?o0 |- ?g =>
    unfold if_not_throw in I;
    if_unmonad k; (* Deal with the [if_ter]. *)
    match goal with
      I : match res_type ?r with
          | restype_normal => ?C1
          | restype_break => ?C2
          | restype_continue => ?C3
          | restype_return => ?C4
          | restype_throw => ?C5
          end = ?o0,
      I' : _ = result_out (out_ter ?s ?r) |- _ =>
      let rt := fresh "rt" in
      sets_eq <- rt: (res_type r);
      let T := fresh "T" in
      tests_basic T: (rt = restype_throw);
      [ rewrite T in * |- *; clear T
      | let I'' := fresh "R" in
        asserts I'': (C1 = o0);
        [ destruct rt; tryfalse; auto*
        | clear I; rename I'' into I]]
    end

  | I : if_object ?o ?K = ?o0 |- ?g =>
    unfold if_object in I;
    if_unmonad k; (* Deal with the [if_value]. *)
    match goal with
      I : match ?v with (* Does not work *)
          | value_prim _ => ?C1
          | value_object l => ?C2
          end = ?o0 |- _ =>
      let v' := fresh "v" in
      sets_eq <- v': v;
      destruct v';
      [k I|]
    end

  end.

Ltac unfold_func vs0 :=
  match vs0 with (@boxer ?T ?t) :: ?vs =>
    let t := constr:(t : T) in
    first
      [ match goal with
        | I : context [ t ] |- _ => unfolds in I
        end | unfold_func vs ]
  end.

Ltac unmonad_with IHe IHs IHp IHel IHc IHcf :=
  repeat first
    [ if_unmonad ltac:(fun I => try inverts I)
    | try unfold_func (>> run_expr_access run_expr_function run_expr_new run_expr_call run_unary_op run_binary_op run_expr_conditionnal run_expr_assign) ];
  repeat match goal with
  | I : runs_type_expr ?runs ?S ?C ?e = ?o |- _ =>
    unfold runs_type_expr in I
  | I : run_expr ?num ?S ?C ?e = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHe (rm I)
  | I : runs_type_stat ?runs ?S ?C ?t = ?o |- _ =>
    unfold runs_type_stat in I
  | I : run_stat ?num ?S ?C ?t = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHs (rm I)
  | I : runs_type_prog ?runs ?S ?C ?p = ?o |- _ =>
    unfold runs_type_prog in I
  | I : run_prog ?num ?S ?C ?p = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHp (rm I)
  | I : run_elements ?num ?S ?C ?rv ?els = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHel (rm I)
  | I : runs_type_call ?runs ?S ?C ?B ?vs = ?o |- _ =>
    unfold runs_type_call in I
  | I : run_call ?num ?S ?C ?B ?vs = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHc (rm I)
  | I : runs_type_call_full ?runs ?S ?C ?l ?v ?vs = ?o |- _ =>
    unfold runs_type_call_full in I
  | I : run_call_full ?num ?S ?C ?l ?v ?vs = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHcf (rm I)
  end.

Ltac unmonad :=
  let IHe := findHyp follow_expr in
  let IHs := findHyp follow_stat in
  let IHp := findHyp follow_prog in
  let IHel := findHyp follow_elements in
  let IHc := findHyp follow_call in
  let IHcf := findHyp follow_call_full in
  unmonad_with IHe IHs IHp IHel IHc IHcf.


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

Lemma res_type_res_overwrite_value_if_empty : forall rv R,
  res_type R = res_type (res_overwrite_value_if_empty rv R).
Proof.
  introv. destruct R. unfold res_overwrite_value_if_empty. simpl.
  cases_if; reflexivity.
Qed.


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
  runs_type_correct (runs num) (run_elements num).
Proof.

  induction num.
   constructors; introv R; inverts R.

   lets [IHe IHs IHp IHel IHc IHcf]: (rm IHnum).
   constructors.

   (* run_expr *)
   intros S C e S' res R. destruct e; simpl in R; unmonad.
    (* this *)
    apply~ red_expr_this.
    (* identifier *)
    skip. (* apply~ red_expr_identifier. *)
    (* literal *)
    skip. (* apply~ red_expr_literal. *)
    (* object *)
    skip.
    (* function *)
    skip.
    (* access *)
    skip.
    (* member *)
    apply~ red_expr_member.
    (* new *)
    skip.
    (* call *)
    skip. skip. skip.
    (* unary_op *)
    skip.
    (* binary_op *)
    skip.
    (* conditionnal *)
    skip.
    (* assign *)
    skip. skip.

   (* run_stat *)
   skip.

   (* run_prog *)
   intros S C p S' res R. destruct p as [str es]. simpls.
   forwards RC: IHel R. apply~ red_prog_prog.

   (* run_elements *)
   intros rv S C es S' res R. destruct es; simpls.
    inverts R. apply~ red_prog_1_nil.
    destruct e.
     (* stat *)
     unmonad.
      (* throw *)
      applys~ red_prog_1_cons_stat RC.
       apply~ red_prog_abort. constructors~. absurd_neg.
       absurd_neg.
      (* otherwise *)
      applys~ red_prog_1_cons_stat RC.
       apply~ red_prog_2. rewrite~ EQrt. discriminate.
       skip. (* destruct r. simpls. substs. cases_if.
        substs. unfold res_overwrite_value_if_empty. cases_if. simpls. apply~ red_prog_3. *)
     (* func_decl *)
     forwards RC: IHel R. apply~ red_prog_1_cons_funcdecl.

   (* run_call *)
   skip.

   (* run_call_full *)
   intros l vs S C v S' res R. simpls.
   skip.

Qed.

