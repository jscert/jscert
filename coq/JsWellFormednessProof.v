Set Implicit Arguments.
Require Export JsWellFormednessDef JsPrettyRules JsInit JsSyntaxInfos.


Hint Constructors Forall wf_expr wf_prog wf_stat wf_var_decl wf_ext_expr wf_ext_stat wf_ext_prog state_of_out.

Tactic Notation "rconstructors" := repeat constructors.
Tactic Notation "rconstructors" "*" := repeat (constructors; auto_star).


(*lemmas about add_info_prog and prog_intro_strictness*)

(*for now this holds, but i'm not sure it's supposed to*)
Lemma wf_add_infos_prog : forall (S:state) (str str':strictness_flag) (p:prog),
  wf_prog S str p ->
  wf_prog S (str'||str) (add_infos_prog str' p). 
Proof.
  introv Hp. inverts Hp. induction l0; simple*.
  inverts* H.
  forwards H: IHl0 H3. constructor~. constructor~.
  (*head*)
    inverts H2. simpl. apply wf_element_stat. inverts H0. simpl.
    (*expr*)
      apply wf_stat_expr.
      clear IHl0 H3 H l0.
      induction e; inverts* H1; simple*.
    (*vardecl*)
      induction l1; simpl; apply~ wf_stat_var_decl. constructor.
      inverts H1. destruct a. destruct o. apply wf_var_decl_some.
        inverts H4. induction e; inverts H1; simple*.
        constructor.
      inverts H1. apply IHl1 in H5. inverts* H5.
  (*induction*)
    forwards M: IHl0 H3.
    inverts* M.
Qed.


Lemma prog_strictness_add_infos_prog : 
  forall (p:prog) (str':strictness_flag),
    prog_intro_strictness (add_infos_prog str' p) = str' || (prog_intro_strictness p).
Proof.
  introv.
  destruct p. subst.
  simpl.
  reflexivity.
Qed.


Lemma add_infos_prog_false :
  forall (p:prog),
    prog_intro_strictness (add_infos_prog strictness_false p) = prog_intro_strictness p.
Proof.
  introv. destruct p. subst. simpl. destruct s;reflexivity.
Qed.


Lemma wf_prog_intro_strictness : forall (S:state) (str:strictness_flag) (p:prog),
  wf_prog S str p ->
  wf_prog S (prog_intro_strictness p) p.
Proof.
  introv Hp. inverts keep Hp. simpl. auto.
Qed.




(*lemmas : if S' extends S and X is wf in S, it is in S' too*)
(* for X=expr, stat, prog... *)

Lemma wf_expr_state_extends : forall (S S':state) (str:strictness_flag) (e:expr),
  state_extends S' S ->
  wf_expr S str e ->
  wf_expr S' str e.
Proof.
  introv Hext HS. induction HS; constructor*.
Qed.


Lemma wf_var_decl_state_extends : forall (S S':state) (str:strictness_flag) (vd:string*option expr),
  state_extends S' S ->
  wf_var_decl S str vd ->
  wf_var_decl S' str vd.
Proof.
  introv Hext HS. induction HS; constructor*; eapply wf_expr_state_extends; eauto.
Qed. 


Lemma wf_stat_state_extends : forall (S S':state) (str:strictness_flag) (t:stat),
  state_extends S' S ->
  wf_stat S str t ->
  wf_stat S' str t.
Proof.
  introv Hext HS. induction HS; constructor*; try eapply wf_expr_state_extends; eauto.
  induction l; constructor; inverts H; try eapply wf_var_decl_state_extends; eauto.
Qed.


Lemma wf_element_state_extends : forall (S S':state) (str:strictness_flag) (el:element),
  state_extends S' S ->
  wf_element S str el ->
  wf_element S' str el.  
Proof.
  introv Hext HS. induction HS; constructor*; eapply wf_stat_state_extends; eauto.
Qed.


Lemma wf_prog_state_extends : forall (S S':state) (str:strictness_flag) (p:prog),
  state_extends S' S ->
  wf_prog S str p ->
  wf_prog S' str p.
Proof.
  introv Hext HS. inverts HS; constructor*. induction l0; constructor*; inverts* H; eapply wf_element_state_extends; eauto.
Qed.


Lemma wf_value_state_extends : forall (S S':state) (str:strictness_flag) (v:value),
  state_extends S' S ->
  wf_value S str v ->
  wf_value S' str v.
Proof.
  introv Hext HS. inverts HS; constructor*.
Qed.


Lemma wf_env_loc_state_extends : forall (S S':state) (str:strictness_flag) (L:env_loc),
  state_extends S' S ->
  wf_env_loc S str L ->
  wf_env_loc S' str L.
Proof.
  introv Hext HS. inverts HS; constructor*. apply* Hext.
Qed.


Lemma wf_ref_state_extends : forall (S S':state) (str:strictness_flag) (r:ref),
  state_extends S' S ->
  wf_ref S str r ->
  wf_ref S' str r.
Proof.
  introv Hext HS. inverts HS; constructor*. inverts H; constructor*.
  eapply wf_value_state_extends; eauto.
  eapply wf_env_loc_state_extends; eauto.
Qed.

Lemma wf_resvalue_state_extends : forall (S S':state) (str:strictness_flag) (rv:resvalue),
  state_extends S' S ->
  wf_resvalue S str rv ->
  wf_resvalue S' str rv.
Proof.
  introv Hext HSrv. inverts* HSrv; constructor; inverts H; constructor.
  inverts H0; constructor.
  inverts H; constructor.
  inverts H. unfolds in H0. inverts Hext. apply H1 in H0.
  constructor. auto.
Qed.


Lemma wf_out_state_extends : forall (S S':state) (str:strictness_flag) (o:out),
  state_extends S S' ->(*it's a trap!*)
  wf_out S str o ->
  wf_out S' str o.
Proof.
  introv Hext Ho.
  destruct o; [inverts Ho | apply wf_out_ter]; inverts* Ho; eapply state_extends_trans; eauto.
Qed.






(*other lemmas*)

Lemma wf_out_of_specret_value :  forall (S:state) (str:strictness_flag) (s:specret value) (o:out),
  out_of_specret s = Some o ->
  wf_specret_value S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.

Lemma wf_out_of_specret_int :  forall (S:state) (str:strictness_flag) (s:specret int) (o:out),
  out_of_specret s = Some o ->
  wf_specret_int S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.

Lemma wf_out_of_specret_valuevalue :  forall (S:state) (str:strictness_flag) (s:specret (value*value)) (o:out),
  out_of_specret s = Some o ->
  wf_specret_valuevalue S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.

Lemma wf_out_of_specret_ref :  forall (S:state) (str:strictness_flag) (s:specret ref) (o:out),
  out_of_specret s = Some o ->
  wf_specret_ref S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.

Lemma wf_out_of_specret_full_descriptor :  forall (S:state) (str:strictness_flag) (s:specret full_descriptor) (o:out),
  out_of_specret s = Some o ->
  wf_specret_full_descriptor S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.


Ltac wf_out_of_specret :=
  match goal with
    | [ H:wf_specret_value ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_value
    | [ H:wf_specret_int ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_int
    | [ H:wf_specret_valuevalue ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_valuevalue
    | [ H:wf_specret_ref ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_ref
    | [ H:wf_specret_full_descriptor ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_full_descriptor
  end.


Lemma wf_out_of_ext_expr : forall (S:state) (str:strictness_flag) (e:ext_expr) (o:out),
  out_of_ext_expr e = Some o ->
  wf_ext_expr S str e ->
  wf_out S str o.
Proof.
introv Ho He. inverts He; inverts* Ho; wf_out_of_specret.
Qed.


Lemma wf_out_of_ext_stat : forall (S:state) (str:strictness_flag) (et:ext_stat) (o:out),
  out_of_ext_stat et = Some o ->
  wf_ext_stat S str et ->
  wf_out S str o.
Proof.
  introv Ho Het. inverts Het; inverts Ho; auto.
  destruct sv; inverts H1; inverts* H.
  destruct sr; inverts* H; inverts* H2;inverts* H0. 
  destruct sv; inverts* H; inverts* H2; inverts* H0.
Qed.

Lemma wf_out_of_ext_prog : forall (S:state) (str:strictness_flag) (ep:ext_prog) (o:out),
  out_of_ext_prog ep = Some o ->
  wf_ext_prog S str ep ->
  wf_out S str o.
Proof.
  introv Ho Hep. 
  destruct ep; inverts Ho; inverts* Hep.
Qed.  


(*only true for now*)
(*i use this to remove the funcdecl case in the proof of pr_red_prog*)
Lemma wf_prog_funcdecl_nil : forall (S:state) (str:strictness_flag) (p:prog),
  wf_prog S str p ->
  prog_funcdecl p = nil.
Proof.
  introv Hp.
  destruct p. unfolds. simpl.
  induction l.  auto. inverts Hp.
  inverts H0. forwards: IHl.
    apply wf_prog_intro. auto.
  rewrite map_cons. rewrite concat_cons. rewrite H. rewrite app_nil_r. simpl.
  clear H H3 IHl.
  inverts* H2.
Qed.



Lemma wf_res_overwrite_value_if_empty : forall (S:state) (str:strictness_flag) (rv:resvalue) (R:res),
  wf_resvalue S str rv ->
  wf_res S str R ->
  wf_res S str (res_overwrite_value_if_empty rv R).
Proof.
  introv Hrv HR. inverts HR. inverts Hrv; unfold res_overwrite_value_if_empty; simpl; cases_if; subst;rconstructors*.
Qed.  




Ltac wf_out_change_state :=
  match goal with
    | [ H:state_extends ?S' ?S |- wf_out ?S _ _ ] =>
      apply wf_out_state_extends with S'; [apply H|]
  end.

Ltac wf_out_extends :=
  match goal with
    | [ H:state_extends ?S' ?S , H':wf_out ?S' ?str ?o |- wf_out ?S ?str ?o ] =>
      apply wf_out_state_extends with S'; [apply H|apply H']
  end.



(*Theorems: the initial state and context are wf*)
Theorem wf_state_initial : wf_state state_initial.
Proof.
  split; simpl;
  rewrite Heap.indom_equiv_binds.
  exists object_prealloc_global.
    repeat (try (apply Heap.binds_write_eq; reflexivity); apply Heap.binds_write_neq);
    intro H; inversion H.
  exists (env_record_object_default prealloc_global).
    apply Heap.binds_write_eq.
Qed.


Theorem wf_execution_ctx_initial : forall (str:strictness_flag),
  wf_execution_ctx str (execution_ctx_initial str).
Proof.
  introv.
  reflexivity.
Qed.  






(*Theorems: wf is preserved by reduction*)

Theorem pr_red_spec_value : forall (S:state) (C:execution_ctx) (str:strictness_flag) (es:ext_spec) (s:specret value),
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_spec S str es ->
  red_spec S C es s ->
  wf_specret_value S str s.
Proof.
Admitted.

Theorem pr_red_spec_int : forall (S:state) (C:execution_ctx) (str:strictness_flag) (es:ext_spec) (s:specret int),
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_spec S str es ->
  red_spec S C es s ->
  wf_specret_int S str s.
Proof.
Admitted.

Theorem pr_red_spec_valuevalue : forall (S:state) (C:execution_ctx) (str:strictness_flag) (es:ext_spec) (s:specret (value*value)),
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_spec S str es ->
  red_spec S C es s ->
  wf_specret_valuevalue S str s.
Proof.
Admitted.

Theorem pr_red_spec_ref : forall (S:state) (C:execution_ctx) (str:strictness_flag) (es:ext_spec) (s:specret ref),
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_spec S str es ->
  red_spec S C es s ->
  wf_specret_ref S str s.
Proof.
Admitted.



Ltac wf_impossible_aux :=
match goal with
  | [ H:wf_expr _ _ _ |- _ ] => inversion H; subst
  | [ H:wf_ext_expr _ _ _ |- _ ] => inversion H; subst
end.

Ltac wf_impossible :=
  try solve [wf_impossible_aux;wf_impossible_aux].


Ltac wf_inverts :=
  match goal with
    | [H:wf_out _ _ (out_ter _ _)|-_] => inverts H
    | [H:wf_out _ _ (out_void _)|-_] => inverts H
    | [H:wf_specret_value _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_int _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_valuevalue _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_ref _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_ref _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_ref _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret_ref _ _ (ret _ _)|-_] => inverts H
    | [H:wf_ext_expr _ _ _|-_] => inverts H
  end.

Ltac wf_inverts3a :=
  try (wf_inverts; try (wf_inverts; try wf_inverts)); auto.

Hint Resolve state_extends_refl : core.
Hint Extern 0 (wf_out _ _ _) => wf_out_extends : core.

Hint Extern 0 (wf_out _ _ _ _) => wf_out_change_state : wf_base.
Hint Extern 0 => constructor : wf_base.
Hint Extern 0 => wf_inverts : wf_base.
Hint Resolve pr_red_spec_ref pr_red_spec_value : wf_base.
Hint Extern 1 => wf_inverts3a : wf_base.

Theorem pr_red_expr : forall (S:state) (C:execution_ctx) (ee:ext_expr) (o:out) (str:strictness_flag),
  red_expr S C ee o ->
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_expr S str ee ->
  wf_out S str o.
Proof.
  introv Hred HS HC Hee. induction Hred; wf_impossible; auto. (*this takes a long time*)

  apply* wf_out_of_ext_expr.

  apply* IHHred. eauto with wf_base.

  wf_inverts3a. repeat constructor*.
  
  wf_inverts3a. constructor*. subst. repeat constructor.

  apply* IHHred2. constructor. apply* IHHred1. constructor.  wf_inverts. inverts H1. assumption.
  
  wf_inverts3a. wf_out_change_state. apply* IHHred. repeat constructor*. eapply pr_red_spec_value; eauto. inverts H5. constructor*.

  wf_inverts3a. inverts H1. wf_out_change_state. apply* IHHred2. repeat constructor. eapply wf_resvalue_state_extends; eauto. apply* IHHred1.

  wf_inverts3a. wf_out_change_state. apply* IHHred2. constructors. cases_if; subst; constructor. apply* IHHred1. constructor. inverts H4. eapply wf_resvalue_state_extends; eauto. subst. constructor.

  wf_inverts3a. repeat constructor*. eapply wf_value_state_extends; eauto.

  wf_inverts. inverts H2. apply* IHHred. constructor. eapply pr_red_spec_value; eauto. constructor*.

  wf_inverts3a. wf_out_change_state. apply* IHHred.

  wf_inverts. inverts H0. apply* IHHred2.

  wf_inverts3a. constructor*. constructor*. repeat constructor.

  wf_inverts3a. wf_out_change_state. apply* IHHred. inverts H5. (*maybe wf_inverts*)repeat constructor*. inverts* H1.

  repeat constructor*.

  wf_inverts3a. wf_out_change_state. apply* IHHred2. constructor. inverts H6. inverts* H2 (*idem*). apply* IHHred1. constructor. inverts H6. inverts* H2. destruct r; subst. simpl in H0. subst. inverts H3. inverts H1. auto.

  wf_inverts3a. wf_out_change_state. apply* IHHred.

  wf_inverts3a. wf_out_change_state. apply* IHHred. inverts H5. inverts H1. constructor*. unfolds in H. destruct r; subst. simpl in H. subst. inverts* H2. inverts* H0.

  wf_inverts3a.

  constructor*. repeat constructor.
  
  wf_inverts. inverts H0. apply* IHHred2.

  wf_inverts3a. wf_out_change_state. apply* IHHred. inverts H4. inverts H0. repeat constructor*. 

  wf_inverts3a. constructor*. repeat constructor.
  
  wf_inverts3a. wf_out_change_state. apply* IHHred. constructor. apply* pr_red_spec_value. constructor. inverts H6. assumption.

  wf_inverts3a. constructor*. repeat constructor. 

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a. constructor*. repeat constructor.

  wf_inverts3a. apply* IHHred. constructor. eapply pr_red_spec_int; eauto. constructor~.

  auto with wf_base.

  auto with wf_base.

  auto with wf_base.

  wf_inverts3a. apply* IHHred. inverts H2. constructor~. eapply pr_red_spec_value; eauto. constructor~.
  

Admitted.



Theorem pr_red_stat : forall (S:state) (C:execution_ctx) (et:ext_stat) (o:out) (str:strictness_flag),
  red_stat S C et o ->
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_stat S str et ->
  wf_out S str o.
Proof.
  introv Hred. induction Hred; introv HS HC Het;  try solve [eapply wf_out_of_ext_stat; eauto]; inverts Het; try inverts H0; try solve [inverts* H1].
  (*red_stat_var_decl_nil*)
    constructor*; try apply state_extends_refl; constructor; constructor.
  (*red_stat_var_decl_cons*)
    inverts H1. apply* IHHred2.
    assert (Ho1:wf_out S str o1). apply* IHHred1. 
    inverts keep Ho1. apply wf_stat_var_decl_1 with S'; auto.
      apply Forall_weaken with (wf_var_decl S str); auto. unfolds. intros. eapply wf_var_decl_state_extends; eauto.
  (*red_stat_var_decl_1*)
    inverts H1. eapply wf_out_state_extends; eauto. apply* IHHred. rconstructors.
    apply Forall_weaken with (wf_var_decl S' str); auto. inverts H2; unfolds; intros; auto.
  (*red_stat_var_decl_item_none*)
    constructor*; try apply state_extends_refl; rconstructors*.
  (*red_stat_var_decl_item_some*)
    apply* IHHred. inverts H1. constructor*.
    eapply pr_red_spec_ref; eauto. constructor*.
  (*red_stat_var_decl_item_1*)
    replace (ret S r) with (specret_val S r) in H2.
    inverts H2.
    apply wf_out_state_extends with S; auto.
    apply* IHHred; constructor*.
    eapply pr_red_spec_value; eauto. constructor*. eapply wf_expr_state_extends; eauto. auto.
  (*red_stat_var_decl_item_2*)
    inverts H4.
    apply wf_out_state_extends with S; auto.
    apply* IHHred. constructor*. eapply pr_red_expr; eauto. rconstructors*.
    eapply wf_ref_state_extends; eauto.
  (*red_stat_var_decl_item_3*)
    rconstructors*.
  (*red_stat_expr*)
    apply* IHHred. constructor*. eapply pr_red_spec_value; eauto. constructor*. inverts* H1.
  (*red_stat_expr_1*)
    rconstructors*.
Qed.

 

Theorem pr_red_prog : forall (S:state) (C:execution_ctx) (ep:ext_prog) (o:out) (str:strictness_flag),

  red_prog S C ep o ->
  wf_state S ->
  wf_execution_ctx str C ->
  wf_ext_prog S str ep ->
  wf_out S str o.
Proof.
  introv Hred. inductions Hred; introv HS HC Hep.
  (*case red_prog_abort*)
    eapply wf_out_of_ext_prog; eauto.
  (*case red_javascript_intro_1*)
    inverts Hep. inverts H1. inverts H2.
    forwards: IHHred HC; auto.
  (*case red_prog_nil*)
    apply* wf_out_ter. (*apply state_extends_refl.*)
    apply wf_res_intro; eapply wf_resvalue_empty; auto.
  (*case red_prog_cons*)
    inverts Hep. inverts keep H0. apply Forall_last_inv in H1. inverts H1.
    forwards: IHHred1 HS HC.
    apply wf_prog_basic. apply* wf_prog_intro.
    inverts H1.
    forwards:IHHred2 HS HC.    
    apply wf_prog_1 with S'. 
      apply* IHHred1.
      apply state_of_out_ter.
      eapply wf_element_state_extends; eauto.
      auto.
   (*case red_prog_1_funcdecl*) 
    inverts Hep. inverts H3.
  (*case red_prog_1_stat*)
    inverts Hep. inverts H3. inverts H2. inverts H6. inverts H4. wf_out_change_state.
    apply* IHHred. apply* wf_prog_2.
      eapply pr_red_stat; eauto.
  (*case red_prog_2*)
    inverts Hep. inverts H3.
    apply* wf_out_ter. subst.
    apply* wf_res_overwrite_value_if_empty.
    eapply wf_resvalue_state_extends. eauto.
    auto.
Qed.



(*state_initial because that's what red_javascript does*)
Theorem pr_red_javascript : forall (p:prog) (str:strictness_flag) (o:out),
  red_javascript p o ->
  wf_prog state_initial str p ->
  wf_out state_initial (prog_intro_strictness p) o.
Proof.
  introv Hred Hp. inverts Hred.
  eapply pr_red_prog. eauto.
  (*wf_state_initial*)
    apply wf_state_initial.
  (*wf_execution_ctx_initial*)
    apply wf_execution_ctx_initial.
  (*wf_ext_prog*)
    assert (Ho1:wf_out state_initial (prog_intro_strictness p) o1).
      eapply pr_red_expr.
      (*red_expr*)
        rewrite add_infos_prog_false in H2.
        apply H2.
      (*wf_state_initial*)
        apply wf_state_initial.
      (*wf_execution_ctx_initial*)
        apply wf_execution_ctx_initial.
      (*wf_ext_expr*)
        apply wf_spec_binding_inst.
        rewrite <- add_infos_prog_false.
        eapply wf_prog_intro_strictness.
        apply wf_add_infos_prog.
        apply Hp.  
    inverts keep Ho1.
    eapply wf_javascript_1.
      (*wf_out*)
        auto.
      (*state_of_out*)
        apply state_of_out_ter.
      (*wf_prog*)
        rewrite <- add_infos_prog_false.
        eapply wf_prog_intro_strictness.
        apply wf_add_infos_prog.
        eapply wf_prog_state_extends; eauto.
Qed.
