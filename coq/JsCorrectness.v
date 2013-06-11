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

Ltac rewrite_morph_option :=
  match goal with
  | H : appcontext [ morph_option ?d ?f ?x ] |- _ =>
    let xn := fresh "x" in
    sets_eq <- xn: x;
    destruct xn
  | H : appcontext [ if_some ?op ?f ] |- _ =>
    let xn := fresh "x" in
    sets_eq <- xn: op;
    destruct xn
  end.


(**************************************************************)
(** General Lemmae *)

Lemma res_overwrite_value_if_empty_empty : forall R,
  res_overwrite_value_if_empty resvalue_empty R = R.
Proof. introv. unfolds. cases_if~. destruct R; simpls; inverts~ e. Qed.

Lemma or_idempotent : forall A : Prop, A \/ A -> A.
(* This probably already exists, but I didn't found it. *)
Proof. introv [?|?]; auto. Qed.


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
(** Unfolding Functions *)

Ltac unfold_func vs0 :=
  match vs0 with (@boxer ?T ?t) :: ?vs =>
    let t := constr:(t : T) in
    first
      [ match goal with
        | I : context [ t ] |- _ => unfolds in I
        end | unfold_func vs ]
  end.

Ltac rm_variables :=
  repeat match goal with
  | I : ?x = ?y |- _ =>
    subst x || subst y
  end.

Ltac dealing_follows_with IHe IHs IHp IHel IHc IHcf :=
  repeat first
    [ progress rm_variables
    | unfold_func (>> run_expr_access run_expr_function
                      run_expr_new run_expr_call
                      run_unary_op run_binary_op
                      run_expr_conditionnal run_expr_assign
                      entering_func_code)
    | idtac ];
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

Ltac dealing_follows :=
  let IHe := findHyp follow_expr in
  let IHs := findHyp follow_stat in
  let IHp := findHyp follow_prog in
  let IHel := findHyp follow_elements in
  let IHc := findHyp follow_call in
  let IHcf := findHyp follow_call_full in
  dealing_follows_with IHe IHs IHp IHel IHc IHcf.


(**************************************************************)
(** Monadic Constructors, Lemmae *)

Definition if_regular_lemma (res : result) S0 R0 M :=
  exists S R, res = out_ter S R /\
    ((res_type R <> restype_normal /\ S = S0 /\ R = R0)
      \/ M S R).

Ltac deal_with_regular_lemma H if_out :=
  let Hnn := fresh "Hnn" in
  let HE := fresh "HE" in
  let HS := fresh "HS" in
  let HR := fresh "HR" in
  let HM := fresh "HM" in
  let S' := fresh "S" in
  let R' := fresh "R" in
  lets (S'&R'&HE&[(Hnn&HS&HR)|HM]): if_out (rm H);
  [|repeat match goal with
           | HM : exists x, _ |- _ =>
             let x := fresh x in destruct HM as [x HM]
           end; intuit;
    repeat match goal with
           | H : result_out (out_ter ?S1 ?R1) = result_out (out_ter ?S0 ?R0) |- _ =>
             inverts~ H
           end].

Lemma if_ter_out : forall res K S R,
  if_ter res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' =>
    K S' R' = out_ter S R).
Proof.
  introv H. asserts (S0&R0&E): (exists S R, res = out_ter S R).
  destruct res as [o'| |]; tryfalse. destruct o'; tryfalse. repeat eexists.
  subst. do 2 eexists. splits~.
Qed.

Lemma if_success_out : forall res K S R,
  if_success res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists rt rv rl,
    R' = res_intro rt rv rl /\
    K S' rv = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_ter_out; substs.
   repeat eexists. left~.
   sets_eq t Et: (res_type R0). repeat eexists.
   rewrite~ res_overwrite_value_if_empty_empty in HM.
   destruct t; try solve [ left; inverts HM; rewrite <- Et; splits~; discriminate ].
   right. destruct R0. simpls. repeat eexists. auto*.
Qed.

Lemma if_value_out : forall res K S R,
  if_value res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists rt v rl,
    R' = res_intro rt (resvalue_value v) rl /\
    K S' v = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_ter_out; substs.
   repeat eexists. left~.
   sets_eq t Et: (res_type R0). repeat eexists.
   rewrite~ res_overwrite_value_if_empty_empty in HM.
   destruct t; try solve [ left; inverts HM; rewrite <- Et; splits~; discriminate ].
   right. destruct R0. simpls. destruct res_value; tryfalse.
   repeat eexists. auto*.
Qed.

Lemma if_object_out : forall res K S R,
  if_object res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists rt l rl,
    R' = res_intro rt (resvalue_value (value_object l)) rl /\
    K S' l = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_ter_out; substs.
   repeat eexists. left~.
   sets_eq t Et: (res_type R0). repeat eexists.
   rewrite~ res_overwrite_value_if_empty_empty in HM.
   destruct t; try solve [ left; inverts HM; rewrite <- Et; splits~; discriminate ].
   right. destruct R0. simpls. destruct res_value; tryfalse. destruct v; tryfalse.
   repeat eexists. auto*.
Qed.

Lemma run_error_correct : forall S C ne S' R',
  run_error S ne = out_ter S' R' ->
  red_expr S C (spec_error ne) (out_ter S' R').
Proof.
  introv E. deal_with_regular_lemma E if_object_out; substs.
  unfolds build_error. destruct S as [E L [l S]]. simpls. cases_if; tryfalse.
   inverts HE. false~ Hnn.
  unfolds build_error. destruct S as [E L [l' S]]. simpls.
   apply~ red_spec_error; [|apply~ red_spec_error_1].
   apply~ red_spec_build_error. reflexivity.
   cases_if. inverts HE.
   apply~ red_spec_build_error_1_no_msg.
Qed.

Lemma object_has_prop_correct : forall S C l x b,
  object_has_prop S l x = Some b ->
  red_expr S C (spec_object_has_prop l x) (out_ter S b).
Admitted. (* TODO (May be painful) *)

Lemma out_error_or_cst_correct : forall S C str ne v S' R',
  out_error_or_cst S str (ne : native_error) v = out_ter S' R' ->
  red_expr S C (spec_error_or_cst str ne v) (out_ter S' R').
Proof.
  introv E. unfolds in E. cases_if.
   apply~ red_spec_error_or_cst_true. apply~ run_error_correct.
   inverts E. apply~ red_spec_error_or_cst_false.
Qed.

Lemma run_object_method_correct : forall Z (meth : _ -> Z) S l,
  (exists O, object_binds S l O) ->
  object_method meth S l (run_object_method meth S l).
Proof.
  introv B. unfolds. unfold run_object_method.
  eexists. splits~. apply pick_spec. apply B.
Qed.

Lemma object_get_correct : forall runs run_elements,
  runs_type_correct runs run_elements -> forall S0 C0 v x S R,
  object_get runs S0 C0 v x = out_ter S R ->
  red_expr S0 C0 (spec_object_get v x) (out_ter S R).
Proof.
  introv RC E. destruct v; tryfalse. simpls.
  apply~ red_spec_object_get. apply run_object_method_correct.
   skip. (* TODO:  How can we deal with this? *)
   skip. (* LATER:  There are some arbitrary left there anyway. *)
Qed.

Lemma prim_value_get_correct : forall runs run_elements,
  runs_type_correct runs run_elements -> forall S0 C0 v x S R,
  prim_value_get runs S0 C0 v x = out_ter S R ->
  red_expr S0 C0 (spec_prim_value_get v x) (out_ter S R).
Proof.
  introv RC E. deal_with_regular_lemma E if_object_out; substs.
   skip. (*apply~ red_spec_prim_value_get.*) (* LATER:  There are some arbitrary left there anyway. *)
   skip. (* LATER:  There are some arbitrary left there anyway. *)
Qed.

Lemma env_record_get_binding_value_correct : forall runs run_elements,
  runs_type_correct runs run_elements -> forall S0 C0 L x str S R,
  env_record_get_binding_value runs S0 C0 L x str = out_ter S R ->
  red_expr S0 C0 (spec_env_record_get_binding_value L x str) (out_ter S R).
Proof.
  introv RC E. do 2 unfolds in E.
  rewrite_morph_option; simpls; tryfalse.
  rewrite <- Heap.binds_equiv_read_option in EQx0.
  applys~ red_spec_env_record_get_binding_value EQx0. destruct e.
   rewrite_morph_option; simpls; tryfalse.
    rewrite <- Heap.binds_equiv_read_option in EQx1. destruct p.
    applys~ red_spec_env_record_get_binding_value_1_decl EQx1.
    repeat cases_if.
     apply~ out_error_or_cst_correct.
     inverts E. apply~ red_spec_returns.
   do 2 unfolds in E. rewrite_morph_option; simpls; tryfalse.
    forwards OP: object_has_prop_correct EQx1.
    applys~ red_spec_env_record_get_binding_value_1_object OP.
    cases_if; subst.
     apply~ red_spec_env_record_get_binding_value_obj_2_true.
      applys~ object_get_correct RC.
     apply~ red_spec_env_record_get_binding_value_2_false.
      apply~ out_error_or_cst_correct.
Qed.

Lemma ref_get_value_correct : forall runs run_elements,
  runs_type_correct runs run_elements -> forall S0 C0 rv S R,
  ref_get_value runs S0 C0 rv = out_ter S R ->
  red_expr S0 C0 (spec_get_value rv) (out_ter S R).
Proof.
  introv RC E. destruct rv; tryfalse.
   inverts E. apply~ red_spec_ref_get_value_value.
   tests: (ref_is_property r).
    destruct r as [rb rn rs]; destruct rb as [v|?]; try solve [inverts C; false].
     apply~ red_spec_ref_get_value_ref_b. reflexivity.
     cases_if; destruct v as [()|l]; simpls; try (solve [inverts C; false]);
       cases_if; first [ applys~ prim_value_get_correct RC | applys~ object_get_correct RC ].
    destruct r as [rb rn rs]; destruct rb as [[()|l]|?]; simpls; tryfalse;
      try (false C; first [ solve [left~] | solve [right~] ]).
     apply~ red_spec_ref_get_value_ref_a. constructors. apply~ run_error_correct.
     apply~ red_spec_ref_get_value_ref_c. reflexivity.
     applys~ env_record_get_binding_value_correct RC.
Qed.


(**************************************************************)
(** Monadic Constructors, Tactics *)

(* Unfold monadic cnstructors.  The continuation is called on all aborting cases. *)
Ltac if_unmonad_with :=
  match goal with
  | H : if_success ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma res H if_success_out
  | H : if_value ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma res H if_value_out
  | H : if_object ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma res H if_object_out
  end.

Ltac unmonad :=
  repeat progress (try if_unmonad_with; try dealing_follows).


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


(*
Theorem runs_correct : forall num,
  runs_type_correct (runs num) (run_elements num).
Proof.

  induction num.
   constructors; introv R; inverts R.

   lets [IHe IHs IHp IHel IHc IHcf]: (rm IHnum).
   constructors.

   (* run_expr *)
   intros S C e S' res R. destruct e; simpl in R; unmonad ltac:idtac.
    (* this *)
    apply~ red_expr_this.
    (* identifier *)
    skip. (* apply~ red_expr_identifier.  FIXME:  [spec_identifier_resolution] needs rules! *)
    (* literal *)
    skip. (* apply~ red_expr_literal. FIXME:  [red_expr_literal] takes a noisy argument. *)
    (* object *)
     (* Abort case *)
     skip.
     (* Normal case *)
     skip. (* Needs an intermediate lemma for [init_object]. *)
    (* function *)
    skip.
    (* access *)
    skip.
    (* member *)
    apply~ red_expr_member.
    (* new *)
    skip.
    (* call *)
     (* Abort case *)
     applys~ red_expr_call RC. apply~ red_expr_abort.
      constructors. absurd_neg.
      absurd_neg.
     (* Normal case *)
     skip.
    (* unary_op *)
    skip.
    (* binary_op *)
    skip.
    (* conditionnal *)
    skip.
    (* assign *)
    skip.

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
     unmonad ltac:idtac.
      skip. (*
      (* throw *)
      applys~ red_prog_1_cons_stat RC.
       apply~ red_prog_abort. constructors~. absurd_neg.
       absurd_neg.
      (* otherwise *)
      applys~ red_prog_1_cons_stat RC.
       apply~ red_prog_2. rewrite~ EQrt. discriminate.
       skip. (* destruct r. simpls. substs. cases_if.
        substs. unfold res_overwrite_value_if_empty. cases_if. simpls. apply~ red_prog_3. *) *)
     (* func_decl *)
     forwards RC: IHel R. apply~ red_prog_1_cons_funcdecl.

   (* run_call *)
   skip.

   (* run_call_full *)
   intros l vs S C v S' res R. simpls. unmonad ltac:idtac.
   skip.

Qed.
*)

