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
    (conv : T -> Te)
    (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> result) := forall S C (e : T) S' res,
  run S C e = out_ter S' res ->
  red S C (conv e) (out_ter S' res).

Inductive passing_output {Te A : Type}
    (K : A -> Te) (red : state -> execution_ctx -> Te -> out -> Prop) C
    : passing A -> result -> Prop :=
  | passing_output_normal : forall S a o,
    red S C (K a) o ->
    passing_output K red C (passing_normal S a) o
  | passing_output_abort : forall o,
    passing_output K red C (passing_abort o) o.

Definition follow_spec_passing {T Te A : Type}
    (conv : T -> (A -> Te) -> Te)
    (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> passing A) := forall S C (x : T) (p : passing A),
  run S C x = p -> forall K S' res,
  passing_output K red C p (out_ter S' res) ->
  red S C (conv x K) (out_ter S' res) /\
    (p = passing_abort (out_ter S' res) -> abort (out_ter S' res)).

Definition follow_expr := follow_spec expr_basic red_expr.
Definition follow_stat := follow_spec stat_basic red_stat.
Definition follow_prog := follow_spec prog_basic red_prog.
Definition follow_elements rv :=
  follow_spec (prog_1 rv) red_prog.
Definition follow_call l vs (run : state -> execution_ctx -> value -> result) :=
  forall S C v S' res,
    run S C v = out_ter S' res ->
    red_expr S C (spec_call l v vs) (out_ter S' res) /\ 
    (res_type res = restype_normal -> exists v', res = (v' : value)).
Definition follow_function_has_instance (_ : state -> object_loc -> value -> result) :=
  True. (* TODO *)
Definition follow_stat_while ls e t :=
  follow_spec
    (stat_while_1 ls e t)
    red_stat.
Definition follow_object_get_own_prop l :=
  follow_spec_passing (spec_object_get_own_prop l) red_expr.
Definition follow_object_get_prop l :=
  follow_spec_passing (spec_object_get_prop l) red_expr.
Definition follow_object_proto_is_prototype_of (_ : state -> object_loc -> object_loc -> result) :=
  True. (* TODO *)
Definition follow_equal (_ : state -> (state -> value -> result) -> (state -> value -> result) -> value -> value -> result) :=
  True. (* TODO *)

Record runs_type_correct runs :=
  make_runs_type_correct {
    runs_type_correct_expr : follow_expr (runs_type_expr runs);
    runs_type_correct_stat : follow_stat (runs_type_stat runs);
    runs_type_correct_prog : follow_prog (runs_type_prog runs);
    (*runs_type_correct_elements : forall rv,
      follow_elements rv (fun S C => run_elements runs S C rv);*)
    runs_type_correct_call : forall l vs,
      follow_call l vs (fun S C vthis =>
        runs_type_call runs S C l vthis vs);
    runs_type_correct_function_has_instance :
      follow_function_has_instance (runs_type_function_has_instance runs);
    runs_type_correct_stat_while : forall ls e t,
      follow_stat_while ls e t (fun S C rv =>
        runs_type_stat_while runs S C rv ls e t);
    runs_type_correct_object_get_own_prop : forall l,
      follow_object_get_own_prop l (fun S C =>
        runs_type_object_get_own_prop runs S C l);
    runs_type_correct_object_get_prop : forall l,
      follow_object_get_prop l (fun S C => runs_type_object_get_prop runs S C l);
    runs_type_correct_object_proto_is_prototype_of :
      follow_object_proto_is_prototype_of (runs_type_object_proto_is_prototype_of runs);
    runs_type_correct_equal :
      follow_equal (runs_type_equal runs)
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

Ltac name_object_method :=
  match goal with
  | |- appcontext [ run_object_method ?meth ?S ?l ] =>
    let B := fresh "B" in
    sets_eq <- B: (run_object_method meth S l)
  | H : appcontext [ run_object_method ?meth ?S ?l ] |- _ =>
    let B := fresh "B" in
    sets_eq <- B: (run_object_method meth S l)
  end.

Ltac name_passing_def :=
  match goal with
  | H : appcontext [ passing_def ?o ?K ] |- _ =>
    let p := fresh "p" in
    sets_eq <- p: (passing_def o K)
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

Lemma passing_output_trans {Te A : Type} :
  forall (red : state -> execution_ctx -> Te -> out -> Prop) C K K' (p : passing A) o,
  (forall S C a,
    red S C (K' K a) o ->
    red S C (K a) o) ->
  passing_output (K' K) red C p o ->
  passing_output K red C p o.
Proof. introv I R. inverts R; constructors*. Qed.

Lemma and_impl_left : forall P1 P2 P3 : Prop,
  (P1 -> P2) ->
  P1 /\ P3 ->
  P2 /\ P3.
Proof. auto*. Qed.

Ltac applys_and_base L :=
  applys~ and_impl_left; [applys L|].

Tactic Notation "applys_and" constr(E) :=
  applys_and_base (>> E).

Tactic Notation "applys_and" constr(E) constr(A1) :=
  applys_and_base (>> E A1).

Tactic Notation "applys_and" constr(E) constr(A1) constr(A2) :=
  applys_and_base (>> E A1 A2).

Tactic Notation "applys_and" constr(E) constr(A1) constr(A2) constr(A3) :=
  applys_and_base (>> E A1 A2 A3).

Ltac constructors_and :=
  let H := fresh in
  eapply and_impl_left; [ intro H; constructors; exact H |].


(**************************************************************)
(** Unfolding Tactics *)

Ltac unfold_func vs0 :=
  match vs0 with (@boxer ?T ?t) :: ?vs =>
    let t := constr:(t : T) in
    first
      [ match goal with
        | I : context [ t ] |- _ => unfolds in I
        end | unfold_func vs ]
  end.

Ltac fold_runs_type := (* Does not work. *)
  match goal with
  | H : appcontext [ let (runs_type_expr, _, _, _, _, _, _, _, _, _) := ?r in
                     runs_type_expr ] |- _ =>
    fold (runs_type_expr r) in H
  end.

Ltac rm_variables :=
  repeat match goal with
  | I : ?x = ?y |- _ =>
    match type of x with
    | passing ?a => idtac (* Given the form of the invariant, this may not be that a good idea. *)
    | _ => subst x || subst y
    end
  | H : ~ False |- _ => clear H (* Some tactics may yield this. *)
  | H : True |- _ => clear H
  end.

Ltac dealing_follows_with IHe IHs IHp (*IHel*) IHc IHhi IHw IHowp IHop IHpo :=
  repeat first
    [ progress rm_variables
    | unfold_func (>> run_expr_access run_expr_function
                      run_expr_new run_expr_call
                      run_unary_op run_binary_op
                      run_expr_conditionnal run_expr_assign
                      entering_func_code)
    | fold_runs_type ];
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
  (*| I : run_elements ?num ?S ?C ?rv ?els = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHel (rm I)*)
  | I : runs_type_call ?runs ?S ?C ?l ?v ?vs = ?o |- _ =>
    unfold runs_type_call in I
  | I : run_call ?runs ?S ?C ?l ?v ?vs = ?o |- _ =>
    let RC := fresh "RC" in
    forwards~ RC: IHc (rm I)
  | I : runs_type_object_get_own_prop ?runs ?S ?C ?l ?x = ?p |- _ =>
    let RC := fresh "RC" in
    lets~ RC: IHowp (rm I)
  | I : runs_type_object_get_prop ?runs ?S ?C ?l ?x = ?p |- _ =>
    let RC := fresh "RC" in
    lets~ RC: IHop (rm I)
  (* TODO:  Complete. *)
  end.

Ltac dealing_follows :=
  let IHe := findHyp follow_expr in
  let IHs := findHyp follow_stat in
  let IHp := findHyp follow_prog in
  (*let IHel := findHyp follow_elements in*)
  let IHc := findHyp follow_call in
  let IHhi := findHyp follow_function_has_instance in
  let IHw := findHyp follow_stat_while in
  let IHowp := findHyp follow_object_get_own_prop in
  let IHop := findHyp follow_object_get_prop in
  let IHpo := findHyp follow_object_proto_is_prototype_of in
  dealing_follows_with IHe IHs IHp (*IHel*) IHc IHhi IHw IHowp IHop IHpo.


(**************************************************************)
(** Monadic Constructors, Lemmae *)

Definition if_regular_lemma (res : result) S0 R0 M :=
  exists S R, res = out_ter S R /\
    ((res_type R <> restype_normal /\ S = S0 /\ R = R0)
      \/ M S R).

Ltac simpl_after_regular_lemma :=
  repeat match goal with
         | HM : exists x, _ |- _ =>
           let x := fresh x in destruct HM as [x HM]
         end; intuit;
  repeat match goal with
         | H : result_out (out_ter ?S1 ?R1) = result_out (out_ter ?S2 ?R2) |- _ =>
           inverts~ H
         end.

Ltac deal_with_regular_lemma H if_out :=
  let Hnn := fresh "Hnn" in
  let HE := fresh "HE" in
  let HS := fresh "HS" in
  let HR := fresh "HR" in
  let HM := fresh "HM" in
  let S' := fresh "S" in
  let R' := fresh "R" in
  lets (S'&R'&HE&[(Hnn&HS&HR)|HM]): if_out (rm H);
  [|simpl_after_regular_lemma].

Ltac deal_with_regular_lemma_run H if_out :=
  let Hnn := fresh "Hnn" in
  let HE := fresh "HE" in
  let HS := fresh "HS" in
  let HR := fresh "HR" in
  let HM := fresh "HM" in
  let S' := fresh "S" in
  let R' := fresh "R" in
  forwards (S'&R'&HE&[(Hnn&HS&HR)|HM]): if_out (rm H);
  [try solve [ constructors~ ] | | simpl_after_regular_lemma].

Lemma if_ter_out : forall res K S R,
  if_ter res K = out_ter S R ->
  exists S' R', res = out_ter S' R' /\ K S' R' = out_ter S R.
Proof.
  introv H. asserts (S0&R0&E): (exists S R, res = out_ter S R).
    destruct res as [o'| | |]; tryfalse. destruct o'; tryfalse. repeat eexists.
  subst. do 2 eexists. splits~.
Qed.

Ltac deal_with_ter H :=
  let HE := fresh "HE" in
  let HR := fresh "HR" in
  let S' := fresh "S" in
  let R' := fresh "R" in
  forwards (S'&R'&HR&HE): if_ter_out (rm H);
  simpl_after_regular_lemma.

Lemma if_success_out : forall res K S R,
  if_success res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists rv,
    R' = res_normal rv /\
    K S' rv = out_ter S R).
Proof.
  introv H. deal_with_ter H; substs.
  sets_eq t Et: (res_type R0). repeat eexists.
  rewrite~ res_overwrite_value_if_empty_empty in HE.
  destruct t; try solve [ left; inverts HE; rewrite <- Et; splits~; discriminate ].
  unfolds in HE. cases_if. right. destruct R0. simpls. substs. repeat eexists. auto*.
Qed.

Lemma if_value_out : forall res K S R,
  if_value res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists v,
    R' = res_val v /\
    K S' v = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_success_out; substs.
   repeat eexists. left~.
   destruct~ rv; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma if_object_out : forall res K S R,
  if_object res K = out_ter S R ->
  if_regular_lemma res S R (fun S' R' => exists l,
    R' = res_val (value_object l) /\
    K S' l = out_ter S R).
Proof.
  introv H. deal_with_regular_lemma H if_value_out; substs.
   repeat eexists. left~.
   destruct~ v; tryfalse. repeat eexists. right. eexists. auto*.
Qed.

Lemma passing_def_out : forall (A B : Type) bo (K : B -> passing A) (p : passing A),
  passing_def bo K = p ->
  (exists b, bo = Some b /\ K b = p) \/
  (exists res, bo = None /\ p = passing_abort res /\ forall o, (o : result) <> res).
Proof. introv E. destruct* bo. right. eexists. splits*. discriminate. Qed.

Lemma passing_defined_out : forall (A B : Type) (p : passing B) K (pr : passing A),
  passing_defined p K = pr ->
  (exists S0 b, p = passing_normal S0 b /\ K S0 b = pr) \/
  (exists res, p = passing_abort res /\ pr = passing_abort res).
Proof. introv E. destruct* p. Qed.

Lemma passing_success_out : forall (A : Type) res K (p : passing A),
  passing_success res K = p ->
  (exists S0 rv, res = out_ter S0 (rv : resvalue) /\
                 K S0 rv = p) \/
  (exists res' S0 rv ls, p = passing_abort res' /\ (forall o, (o : result) <> res') /\
                      res = out_ter S0 (res_intro restype_normal rv ls) /\
                      ls <> label_empty) \/
  (exists o, res = result_out o /\ p = passing_abort res /\ abort o) \/
  (p = passing_abort res /\ forall o, res <> o).
Proof.
  introv E. destruct~ res; try solve [branch 4; splits~; discriminate].
  destruct~ o.
   branch 3. eexists. splits~. constructors.
  destruct r as [T R L]. destruct~ T; try solve [ branch 3;
    eexists; splits~; constructors; absurd_neg ]. simpls.
  cases_if.
   branch 1. substs. repeat eexists.
   branch 2. substs. repeat eexists; auto*. discriminate.
Qed.

Lemma passing_value_out : forall (A : Type) res K (p : passing A),
  passing_value res K = p ->
  (exists S0 v, res = out_ter S0 (v : value) /\
                 K S0 v = p) \/
  (exists res' S0 rv ls, p = passing_abort res' /\ (forall o, (o : result) <> res') /\
                      res = out_ter S0 (res_intro restype_normal rv ls) /\
                      (ls <> label_empty \/ forall v, rv <> v)) \/
  (exists o, res = result_out o /\ p = passing_abort res /\ abort o) \/
  (p = passing_abort res /\ forall o, res <> o).
Proof.
  introv E. destruct~ res; try solve [branch 4; splits~; discriminate].
  destruct~ o.
   branch 3. eexists. splits~. constructors.
  destruct r as [T R L]. destruct~ T; try solve [ branch 3;
    eexists; splits~; constructors; absurd_neg ]. simpls.
  cases_if; destruct R; subst; try (
    branch 2; repeat eexists;
    [ discriminate | solve [left*] || solve [try right; discriminate] ]).
  branch 1. repeat eexists.
Qed.

Lemma run_error_correct : forall S ne S' R',
  run_error S ne = out_ter S' R' ->
  (forall C, red_expr S C (spec_error ne) (out_ter S' R')) /\
  res_type R' <> restype_normal.
Proof.
  introv E. deal_with_regular_lemma E if_object_out; substs.
  unfolds build_error. destruct S as [E L [l S]]. simpls. cases_if; tryfalse.
   inverts HE. false~ Hnn.
  unfolds build_error. destruct S as [E L [l' S]]. simpls.
   split; [|discriminate]. introv. apply~ red_spec_error; [|apply~ red_spec_error_1].
   apply~ red_spec_build_error. reflexivity.
   cases_if. inverts HE.
   apply~ red_spec_build_error_1_no_msg.
Qed.

Lemma out_error_or_cst_correct : forall S C str ne v S' R',
  out_error_or_cst S str (ne : native_error) v = out_ter S' R' ->
  red_expr S C (spec_error_or_cst str ne v) (out_ter S' R').
Proof.
  introv E. unfolds in E. cases_if.
   apply~ red_spec_error_or_cst_true. apply~ run_error_correct.
   inverts E. apply~ red_spec_error_or_cst_false.
Qed.

Lemma run_object_method_correct : forall Z (meth : _ -> Z) S l (z : Z),
  run_object_method meth S l = Some z ->
  object_method meth S l z.
Proof.
  introv B. unfolds. forwards (O&Bi&E): option_map_some_back B.
  forwards: @pick_option_correct Bi. exists* O.
Qed.

Lemma object_has_prop_correct : forall runs,
  runs_type_correct runs -> forall S S1 C l x b,
  object_has_prop runs S C l x = passing_normal S1 b ->
  red_expr S C (spec_object_has_prop l x) (out_ter S1 b).
Proof.
  introv RC E. unfolds in E. name_object_method.
  destruct B as [B|]; simpls; tryfalse.
  destruct B.
  applys red_spec_object_has_prop.
    applys* run_object_method_correct.
    apply red_spec_object_has_prop_1_default.
     apply passing_defined_out in E.
     cases E; clear Eq E.
       destruct e as [S0 [b0 [He1 He2]]].
        inverts He2.
        lets [_ _ _ _ _ _ _ RCo _ _] : RC.
        forwards H: (rm RCo) l.
        unfolds follow_object_get_prop.
        unfolds follow_spec_passing.
         applys~ H.
         rewrite He1.
         applys~ (passing_output_normal spec_object_has_prop_2).
         applys~ red_spec_object_has_prop_2.
         rew_refl.
         cases_if~.
           rewrite~ isTrue_true.
           rewrite~ isTrue_false.
       destruct e as [res [He1 He2]]; tryfalse.
Qed.

Lemma run_object_get_correct : forall runs,
  runs_type_correct runs -> forall S0 C0 l x S R,
  run_object_get runs S0 C0 l x = out_ter S R ->
  red_expr S0 C0 (spec_object_get l x) (out_ter S R) /\
  (res_type R = restype_normal -> exists v, R = (v : value)).
Proof.
  introv RC E.
  unfolds in E.
  name_object_method.
  destruct B as [B|]; simpls; tryfalse.
  forwards OM: run_object_method_correct (rm EQB).
  lets [_ _ _ _ _ _ _ RCo _ _] : RC.
  forwards H: (rm RCo) l.
  unfolds follow_object_get_prop.
  unfolds follow_spec_passing.
  destruct B; simpls; tryfalse.
  sets_eq p: (runs_type_object_get_prop runs S0 C0 l x).
  splits.
    applys~ red_spec_object_get (rm OM).
     destruct p.
      apply red_spec_object_get_1_default.       
      applys~ H.
      rewrite <- EQp. simpls. clear EQp. apply passing_output_normal.
      destruct f; simpls; inverts E.
        apply red_spec_object_get_2_undef.
        destruct a; simpls.
          inverts H1. applys~ red_spec_object_get_2_data.
          applys red_spec_object_get_2_accessor.
           destruct (attributes_accessor_get a).
             destruct p; inverts H1.
              apply red_spec_object_get_3_accessor_undef.
             apply red_spec_object_get_3_accessor_object.
              lets [_ _ _ RCa _ _ _ _ _ _] : RC.
              specialize (RCa o nil).
              unfolds follow_call.
              applys~ RCa.
      apply red_spec_object_get_1_default.
       applys~ H.
       rewrite <- EQp. simpls.
       rewrite E.
       apply (passing_output_abort (spec_object_get_2 l l)).
    introv Hrn; destruct p.
      destruct f; simpls; inverts* E.
      destruct a; simpls; invert H1.
        introv _ _; auto*.
        introv H1; destruct (attributes_accessor_get a).
          destruct p; inverts* H1.
          lets [_ _ _ RCa _ _ _ _ _ _] : RC.
           specialize (RCa o nil).
           unfolds follow_call. applys~ RCa s C0 l S.
      simpls.
       false.
       asserts Hab : (abort (out_ter S R)).
       symmetry in EQp.
       applys~ H EQp  (spec_object_get_2 l l).
       rewrite E.
       apply (passing_output_abort (spec_object_get_2 l l)).
       substs~.
      inverts~ Hab.
Qed.

Lemma env_record_get_binding_value_correct : forall runs,
  runs_type_correct runs -> forall S0 S C0 L rn rs R,
  env_record_get_binding_value runs S0 C0 L rn rs = out_ter S R ->
  red_expr S0 C0 (spec_env_record_get_binding_value L rn rs) (out_ter S R) /\
  (res_type R = restype_normal -> exists v, R = (v : value)).
Proof.
  introv RC E.
Admitted. (* TODO *)

Lemma ref_get_value_correct : forall runs,
  runs_type_correct runs -> forall S0 C0 rv S R,
  ref_get_value runs S0 C0 rv = out_ter S R ->
  red_expr S0 C0 (spec_get_value rv) (out_ter S R) /\
  (res_type R = restype_normal -> exists v, R = (v : value)).
Proof.
  introv RC E. destruct rv; tryfalse.
   inverts E. splits. apply~ red_spec_ref_get_value_value. intros. auto*.
   tests: (ref_is_property r).
    destruct r as [rb rn rs]; destruct rb as [v|?]; try solve [inverts C; false].
      split.
       apply~ red_spec_ref_get_value_ref_b. reflexivity.
        cases_if; destruct v as [()|l]; simpls; try (solve [inverts C; false]);
         cases_if; first [ applys~ prim_value_get_correct RC | applys~ run_object_get_correct RC ].
       intro Rn. destruct v. destruct p; simpls; tryfalse;
         try solve [ forwards~ (_&?): run_error_correct E; false ]; cases_if; tryfalse.
        simpls. cases_if. forwards~ (_&?): run_object_get_correct RC E.
    destruct r as [rb rn rs]; destruct rb as [[()|l]|?]; simpls; tryfalse;
      try (false C; first [ solve [left~] | solve [right~] ]); split.
     apply~ red_spec_ref_get_value_ref_a. constructors. apply~ run_error_correct.
     introv Eq. forwards~ (_&?): run_error_correct E. false.
     apply~ red_spec_ref_get_value_ref_c. reflexivity.
      applys~ env_record_get_binding_value_correct RC.
     intros. forwards~ (_&?): env_record_get_binding_value_correct E.
Qed.

Lemma if_success_value_out : forall runs,
  runs_type_correct runs -> forall res0 K S C R,
  if_success_value runs C res0 K = out_ter S R ->
  if_regular_lemma res0 S R (fun S' R' => (exists rv S'' R'',
    R' = res_normal rv /\
    red_expr S' C (spec_get_value rv) (out_ter S'' R'') /\
    res_type R'' <> restype_normal /\
    R = R'' /\ S = S'') \/ (exists rv S'' v,
    R' = res_normal rv /\
    red_expr S' C (spec_get_value rv) (out_ter S'' (v : value)) /\
    K S'' v = out_ter S R)).
Proof.
  introv RC H. deal_with_regular_lemma H if_success_out; substs; repeat eexists.
   branch~ 1.
   deal_with_regular_lemma H0 if_success_out; substs.
    forwards~ (GV&GVC): ref_get_value_correct HE. branch 2. repeat eexists; auto*.
    forwards~ (GV&GVC): ref_get_value_correct HE. branch 3.
     forwards~ (v&Ev): GVC. inverts Ev. repeat eexists; auto*.
Qed.


(**************************************************************)
(** Monadic Constructors, Tactics *)

Ltac other_follows :=
  try match goal with
  | H : run_object_method ?meth ?S ?l = Some ?z |- _ =>
    let R := fresh "R" in (* Maybe this usage of [fresh] is not very serious... *)
    try rewrite H in * |- *;
    forwards R: @run_object_method_correct (rm H)
  end.

Ltac unmonad_passing :=
  let Ep := fresh "Ep" in
  let No := fresh "No" in
  let deal_with_fail_case :=
    try match goal with
    | H : passing_output ?K ?red ?C ?p ?res |- _ =>
      first [ solve [ rewrite Ep in H; inverts H; false* No ]
            | solve [ substs; inverts H; constructors~ ] ]
    end
  in try match goal with
  (* TODO:  Factorize the following tactics. *)
  | H : passing_def ?bo ?K = ?p |- _ =>
    let E := fresh "E" in
    forwards [(?&?&E)|(?&?&Ep&No)]: @passing_def_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_defined ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let p := fresh "p" in
    let E := fresh "E" in
    forwards [(S&?&?&E)|(?&Ep&?)]: @passing_defined_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_success ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let rv := fresh "rv" in
    let E := fresh "E" in
    let Eo := fresh "Eo" in
    forwards [(S&rv&Eo&E)|[(?&S&rv&?&Ep&No&?&?)|[(?&?&E&?)|(E&No)]]]: @passing_success_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  | H : passing_value ?p ?K = ?p0 |- _ =>
    let S := fresh "S" in
    let v := fresh "v" in
    let E := fresh "E" in
    let Eo := fresh "Eo" in
    forwards [(S&v&Eo&E)|[(?&S&rv&?&Ep&No&?&?)|[(?&?&E&?)|(E&No)]]]: @passing_value_out (rm H);
    deal_with_fail_case;
    simpl_after_regular_lemma
  end;
  dealing_follows;
  other_follows.

(* Unfold monadic cnstructors.  The continuation is called on all aborting cases. *)
Ltac unmonad :=
  try match goal with
  | H : if_ter ?res ?K = result_out ?o' |- _ =>
    deal_with_ter H
  | H : if_success ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma H if_success_out
  | H : if_value ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma H if_value_out
  | H : if_object ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma H if_object_out
  | H : if_success_value ?runs ?C ?res ?K = result_out ?o' |- _ =>
    deal_with_regular_lemma_run H if_success_value_out
  | H : result_out (out_ter ?S1 ?res1) = result_out (out_ter ?S2 ?res2) |- _ =>
    inverts H
  | H : passing_normal ?S1 ?D1 = passing_normal ?S2 ?D2 |- _ =>
    inverts H
  (* TODO:  Complete. *)
  end;
  dealing_follows;
  other_follows.


(**************************************************************)
(** Operations on environments *)


(**************************************************************)
(** ** Main theorem *)

Ltac abort_expr :=
  apply red_expr_abort;
   [ auto*
   | try solve [constructors; absurd_neg]
   | try solve [absurd_neg]].

Ltac abort_stat :=
  apply red_stat_abort;
   [ auto*
   | try solve [constructors; absurd_neg]
   | try solve [absurd_neg]].

Ltac abort_prog :=
  apply red_prog_abort;
   [ auto*
   | try solve [constructors; absurd_neg]
   | try solve [absurd_neg]].


Theorem runs_correct : forall num,
  runs_type_correct (runs num).
Proof.

  induction num.
   constructors; try solve [unfolds~ (* Temporary *)]; introv R; inverts R; introv P; inverts P.

   lets [IHe IHs IHp (*IHel*) IHc IHhi IHw IHowp IHop IHpo]: (rm IHnum).
   constructors.

   (* run_expr *)
   intros S C e S' res R. destruct e; simpl in R; dealing_follows.
    (* this *)
    unmonad. apply~ red_expr_this.
    (* identifier *)
    apply~ red_expr_identifier.
    skip. (* FIXME:  [spec_identifier_resolution] needs rules! *)
    (* literal *)
    unmonad. apply~ red_expr_literal.
    (* object *)
    unfold call_object_new in R. destruct S as [SH SE [fl SF]]. unmonad; simpls.
     (* Abort case *)
     inverts HE. false~ Hnn.
     (* Normal case *)
     unmonad. skip. (* Needs an intermediate lemma for [init_object]. *)
    (* function *)
    skip.
    (* access *)
    skip.
    (* member *)
    apply~ red_expr_member.
    (* new *)
    skip.
    (* call *)
    unmonad.
     (* Abort case *)
     forwards~ RC: IHe (rm HE). applys~ red_expr_call RC. abort_expr.
     (* Normal case *)
     forwards~ RC: IHe (rm HE). applys~ red_expr_call RC.
     skip.
    (* unary_op *)
    destruct~ u; simpls; cases_if; try solve [false~ n].
     (* Delete *)
     unmonad.
      (* Abort case *)
      forwards~ RC: IHe (rm HE). applys~ red_expr_delete RC. abort_expr.
      (* Normal case *)
      forwards~ RC: IHe (rm HE). applys~ red_expr_delete RC.
      destruct rv; try solve [ inverts H0; apply* red_expr_delete_1_not_ref; absurd_neg ].
      cases_if.
       inverts H0. apply* red_expr_delete_1_ref_unresolvable.
       destruct r as [[rbv|rbel] rn rs]; simpls.
        skip. (* TODO:  check in the interpreter that the reference base is neither null nor undefined. *)
        apply~ red_expr_delete_1_ref_env_record. reflexivity.
         skip. (* Needs a lemma [env_record_delete_binding_correct]. *)
     (* Void *)
     unmonad.
      (* Abort case *)
      forwards~ RC: IHe (rm HE). apply~ red_expr_unary_op. simpl. cases_if~; tryfalse.
      applys~ red_spec_expr_get_value RC. abort_expr. abort_expr.
      (* Normal case *)
      forwards~ RC: IHe (rm HE). inverts HM as HM; simpl_after_regular_lemma; rm_variables.
       apply~ red_expr_unary_op. simpl. cases_if~; tryfalse.
        applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
        abort_expr.
       apply~ red_expr_unary_op. simpl. cases_if~; tryfalse.
        applys~ red_spec_expr_get_value RC. applys~ red_spec_expr_get_value_1 H0.
        apply~ red_expr_unary_op_1. apply~ red_expr_unary_op_void.
     (* TypeOf *)
     skip.
     (* Post Incr *)
     skip.
     (* Post Decr *)
     skip.
     (* Pre Incr *)
     skip.
     (* Pre Decr *)
     skip.
     (* Add *)
     skip.
     (* Neg *)
     skip.
     (* Bitwise *)
     skip.
     (* Not *)
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
   skip. (* forwards RC: IHel R. apply~ red_prog_prog. *)

   (* OLD
   (* run_elements *)
   intros rv S C es S' res R. destruct es; simpls.
    inverts R. apply~ red_prog_1_nil.
    destruct e.
     (* stat *)
     unmonad.
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
   *)

   (* run_call *)
   intros l vs S C v S' res R. simpls. unfolds in R. unmonad.
   name_object_method. do 2 (destruct B as [B|]; tryfalse). destruct B; tryfalse.
    (* Call Default *)
    skip.
    (* Call Prealloc *)
    splits.
     apply~ red_spec_call. applys run_object_method_correct EQB.
      apply~ red_spec_call_1_prealloc. unmonad.
      skip.
     skip.

   (* OLD
   (* object_get_builtin *)
   intros v l x S C B S' res R.  destruct~ B; simpls; unmonad.
    (* Default *)
    skip. (* Use: red_spec_object_get_1_default. *)
    (* Function *)
    false. (* Temporary *)
    (* Get Args *)
    false. (* Temporary *)
   *)

   (* HasInstance *)
   skip.

   (* While *)
   intros ls e t S C v S' res R. simpls. unfolds in R. apply~ red_stat_while_1.
   unmonad.
    forwards~ RC: IHe (rm HE). apply~ red_spec_expr_get_value_conv_stat.
     applys~ red_spec_expr_get_value RC. abort_expr.
     abort_stat.
    forwards~ RC: IHe (rm HE). inverts HM as HM; simpl_after_regular_lemma; rm_variables.
     apply~ red_spec_expr_get_value_conv_stat. applys~ red_spec_expr_get_value RC.
       applys~ red_spec_expr_get_value_1 H0.
      abort_stat.
     apply~ red_spec_expr_get_value_conv_stat. applys~ red_spec_expr_get_value RC.
       applys~ red_spec_expr_get_value_1 H0.
      apply~ red_spec_expr_get_value_conv_stat_1. apply* red_spec_to_boolean.
      apply~ red_spec_expr_get_value_conv_stat_2.
      cases_if.
       unmonad. forwards~ RCs: IHs (rm HR). applys~ red_stat_while_2_true RCs.
        apply~ red_stat_while_3. destruct R as [Rt Rv Rl]; simpls.
        tests: (Rt = restype_break).
         cases_if in HE; inverts HE.
          do 2 cases_if; apply~ red_stat_while_4_break.
          apply~ red_stat_while_4_abrupt; try absurd_neg.
        tests: (Rt = restype_continue).
         cases_if in HE; inverts HE.
          forwards~ RCw: IHw (rm H3). do 2 cases_if; applys~ red_stat_while_4_continue RCw.
          apply~ red_stat_while_4_abrupt; try absurd_neg.
        tests: (Rt = restype_normal).
         unfolds in HE. cases_if in HE; tryfalse. forwards~ RCw: IHw (rm HE).
         do 2 cases_if; apply~ red_stat_while_4_continue.
        destruct Rt; tryfalse; inverts HE; apply~ red_stat_while_4_abrupt; absurd_neg.
       unmonad. apply~ red_stat_while_2_false.

   (* GetOwnprop *)
   introv E R. simpls. unfolds in E. unmonad_passing.
    applys_and red_spec_object_get_own_prop R0. name_passing_def.
    asserts Co: (forall K o,
        passing_output K red_expr C p0 o ->
        red_expr S C (spec_object_get_own_prop_1 builtin_get_own_prop_default l x K) o /\
          (p0 = passing_abort o -> abort o)).
      introv R'. unmonad_passing.
      applys_and red_spec_object_get_own_prop_1_default R1. reflexivity.
      rewrite <- E in R'. sets_eq Ao: (Heap.read_option x1 x). destruct Ao; inverts R'.
       splits. apply~ red_spec_object_get_own_prop_2_some_data. absurd_neg.
       splits. apply~ red_spec_object_get_own_prop_2_none. absurd_neg.
    destruct x0.
     inverts E0. apply* Co.
     applys_and red_spec_object_get_own_prop_args_obj. applys_and Co. clear EQp0.
      unmonad_passing. destruct x0.
       substs. inverts R. splits.
        constructors. apply~ red_spec_object_get_own_prop_args_obj_1_undef.
        absurd_neg.
       rewrite H. constructors_and. unmonad_passing.
        destruct x0; simpls; try solve [ substs; inverts R ].
        applys_and red_spec_object_get_own_prop_args_obj_1_attrs R1.
        unmonad_passing.
         applys_and RC. constructors_and. destruct x0.
          applys_and red_spec_object_get_own_prop_args_obj_2_undef.
           applys_and red_spec_object_get_own_prop_args_obj_4.
           inverts~ R; tryfalse. inverts~ H0. splits~. absurd_neg.
          unmonad_passing.
           forwards~ G: run_object_get_correct Eo. constructors~.
            applys_and red_spec_object_get_own_prop_args_obj_2_attrs G. destruct a.
             applys_and red_spec_object_get_own_prop_args_obj_3.
              applys_and red_spec_object_get_own_prop_args_obj_4.
              inverts~ R; tryfalse. splits. inverts~ H0. absurd_neg.
             subst p. inverts R.
           subst p. inverts R. symmetry in H3. rewrite H3 in H0. inverts H0.
            forwards~ G: run_object_get_correct H3. constructors~.
            applys_and red_spec_object_get_own_prop_args_obj_2_attrs G. splits~.
            apply~ red_expr_abort. absurd_neg.
           subst p. inverts R. false* No.
         applys_and RC. rewrite H0 in R. inverts R. splits. constructors.
          forwards*: RC K. constructors.
       substs. inverts R. splits. constructors.
        forwards*: Co K. constructors.

   (* Getprop *)
   introv E R. simpls. unfolds in E. unmonad_passing.
   applys_and red_spec_object_get_prop R0. destruct x0.
    applys_and red_spec_object_get_prop_1_default. unmonad_passing.
     applys_and RC. cases_if.
      subst x0. constructors_and. unmonad_passing.
       applys_and red_spec_object_get_prop_2_undef R1. destruct x0; tryfalse.
        destruct p0; subst p; inverts R. splits.
         apply~ red_spec_object_get_prop_3_null.
         absurd_neg.
        unmonad. splits.
         apply~ red_spec_object_get_prop_3_not_null. apply* RC0.
         apply* RC0.
      destruct x0; tryfalse. subst p. inverts R. constructors_and.
       splits. apply~ red_spec_object_get_prop_2_not_undef. absurd_neg.
     subst p. inverts R. applys_and RC.  splits. constructors.
      forwards*: RC K. constructors.

   (* IsPrototypeOf *)
   skip.

   (* Equal *)
   skip.

Qed.


