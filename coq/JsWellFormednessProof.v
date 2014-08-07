Set Implicit Arguments.
Require Export JsWellFormednessDef.

Ltac auto_star ::= auto_star_default.

Hint Constructors Forall wf_expr wf_prog wf_stat wf_var_decl wf_ext_expr wf_ext_stat wf_ext_prog state_of_out wf_oexpr wf_ostat wf_ostringstat wf_value.

Tactic Notation "rconstructors" := repeat constructors.
Tactic Notation "rconstructors" "*" := repeat (constructors; auto_star).



(*lemmas about add_info_prog and prog_intro_strictness*)

Lemma listmap_liblistmap : forall {X Y:Type} (l:list X) (f:X->Y),
  List.map f l = LibList.map f l.
Proof.
  introv.
  induction l; auto.
  rewrite map_cons. rewrite <- IHl. reflexivity.
Qed.


Lemma wf_add_infos_exp : forall (S:state) (str:strictness_flag) (e:expr),
  wf_expr S str e ->
  wf_expr S str (add_infos_exp str e).
Proof.
  introv H. induction H; constructor*.
Qed.


Definition add_infos_switchclause (str:strictness_flag) (sc:switchclause) := 
  match sc with
    | switchclause_intro e l => switchclause_intro (add_infos_exp str e) (List.map (add_infos_stat str label_set_empty) l)
  end.


Lemma wf_add_infos_stat : forall (S:state) (str:strictness_flag) (labs:label_set) (t:stat),
  wf_stat S str t ->
  wf_stat S str (add_infos_stat str labs t)

with wf_add_infos_switchbody : forall (S:state) (str:strictness_flag) (sb:switchbody),
  wf_switchbody S str sb ->
  wf_switchbody S str (add_infos_switchbody str sb)

with wf_add_infos_switchclause : forall (S:state) (str:strictness_flag) (sc:switchclause),
  wf_switchclause S str sc ->
  wf_switchclause S str (add_infos_switchclause str sc)

with wf_add_infos_ostat : forall (S:state) (str:strictness_flag) (labs:label_set) (ot:option stat),
  wf_ostat S str ot ->
  wf_ostat S str (add_infos_ostat str labs ot)

with wf_add_infos_liststat : forall (S:state) (str:strictness_flag) (labs:label_set) (lt:list stat),
  wf_liststat S str lt ->
  wf_liststat S str (List.map (add_infos_stat str labs) lt)

with wf_add_infos_listswitchclause : forall (S:state) (str:strictness_flag) (lsc:list switchclause),
  wf_listswitchclause S str lsc ->
  wf_listswitchclause S str (List.map (add_infos_switchclause str) lsc).

Proof.
(*proof of wf_add_infos_stat*)
  introv Ht. destruct Ht; simpl; try constructor*;try solve [inverts H; inverts* H0; inverts H1; constructor*; try apply* wf_add_infos_exp]; try apply* wf_add_infos_exp.
  (*stat_var_decl*)
    induction l; simpl; constructor*.
    inverts H. apply IHl in H3. clear IHl.
    destruct a. inverts H2; constructor*. induction H0; constructor*.
    inverts H. apply* IHl. 
  (*stat_return*)
    inverts* H; constructor*. apply* wf_add_infos_exp.
  (*stat_for_var*)
    induction l. auto.
    inverts H.
    simpl. constructor*.
    inverts* H4. constructor*. apply* wf_add_infos_exp.

(*proof of wf_add_infos_switchbody*)
  introv Hsb. destruct Hsb; simpl; constructor; try apply* wf_add_infos_listswitchclause. apply* wf_add_infos_liststat.

(*proof of wf_add_infos_switchclause*)
  introv Hsc. destruct Hsc. constructor. apply* wf_add_infos_exp. apply* wf_add_infos_liststat.

(*proof of wf_add_infos_ostat*)
  introv Hot. destruct Hot; constructor. apply* wf_add_infos_stat.

(*proof of wf_add_infos_liststat*)
  introv Hlt. destruct Hlt; simpl; constructor. apply* wf_add_infos_stat. apply* wf_add_infos_liststat.

(*proof of wf_add_infos_listswitchclause*)
  introv Hlsc. destruct Hlsc; simpl; constructor. apply* wf_add_infos_switchclause. apply* wf_add_infos_listswitchclause.

Qed.


Lemma wf_add_infos_prog_strictness_false : forall (S:state) (str:strictness_flag) (p:prog),
  wf_prog S str p ->
  wf_prog S str (add_infos_prog strictness_false p). 
Proof.
  introv Hp. inverts Hp. induction l0; simple*.
  (*nil*)
    cases_if; constructor*.
  (*a::l0*)
    replace (if str then true else false) with str; [|cases_if; auto].
    inverts* H. forwards* M:IHl0 H3. replace (if str then true else false) with str in M; [|cases_if; auto].
    rconstructors*.
    (*head*)
      clear H3 M IHl0 l0.
      inverts H2. simpl. constructor. apply* wf_add_infos_stat.
    (*induction*)
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

Lemma wf_oexpr_state_extends : forall (S S':state) (str:strictness_flag) (oe:option expr),
  state_extends S' S ->
  wf_oexpr S str oe ->
  wf_oexpr S' str oe.
Proof.
  introv Hext HS. induction HS; constructor*; apply* wf_expr_state_extends.
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
  wf_stat S' str t

with wf_switchbody_state_extends : forall (S S':state) (str:strictness_flag) (sb:switchbody),
  state_extends S' S ->
  wf_switchbody S str sb ->
  wf_switchbody S' str sb

with wf_switchclause_state_extends : forall (S S':state) (str:strictness_flag) (sc:switchclause),
  state_extends S' S ->
  wf_switchclause S str sc ->
  wf_switchclause S' str sc

with wf_ostat_state_extends : forall (S S':state) (str:strictness_flag) (ot:option stat),
  state_extends S' S ->
  wf_ostat S str ot ->
  wf_ostat S' str ot

with wf_ostringstat_state_extends : forall (S S':state) (str:strictness_flag) (ost:option (string*stat)),
  state_extends S' S ->
  wf_ostringstat S str ost ->
  wf_ostringstat S' str ost

with wf_liststat_state_extends : forall (S S':state) (str:strictness_flag) (lt:list stat),
  state_extends S' S ->
  wf_liststat S str lt ->
  wf_liststat S' str lt

with wf_listswitchclause_state_extends : forall (S S':state) (str:strictness_flag) (lsc:list switchclause),
  state_extends S' S ->
  wf_listswitchclause S str lsc ->
  wf_listswitchclause S' str lsc.
Proof.
(*proof of wf_stat_state_extends*)
  introv Hext HS.
  clear wf_switchclause_state_extends wf_listswitchclause_state_extends. 
  destruct HS; constructor*; try solve [inverts* H; try constructor*; try apply* wf_expr_state_extends]; try apply* wf_expr_state_extends.
  induction l; constructor; inverts H; try eapply wf_var_decl_state_extends; eauto.
  inverts* H0; constructor*; apply* wf_expr_state_extends.
  inverts* H1; constructor*; apply* wf_expr_state_extends.
  apply* Forall_weaken. introv HH; apply* wf_var_decl_state_extends.
    inverts* H0; constructor*; apply* wf_expr_state_extends.
    inverts* H1; constructor*; apply* wf_expr_state_extends.

(*proof of wf_switchbody_state_extends*)
  introv Hext HS.
  clear wf_stat_state_extends wf_switchclause_state_extends wf_ostat_state_extends wf_ostringstat_state_extends. 
  destruct HS; constructor*.

(*proof of wf_switchclause_state_extends*)
  introv Hext HS.
  clear wf_stat_state_extends wf_switchbody_state_extends wf_switchclause_state_extends wf_ostat_state_extends wf_ostringstat_state_extends.
  destruct HS; constructor*.
  apply* wf_expr_state_extends.

(*proof of wf_ostat_state_extends*)
  introv Hext HS.
  clear wf_switchbody_state_extends wf_switchclause_state_extends wf_ostat_state_extends wf_ostringstat_state_extends wf_liststat_state_extends wf_listswitchclause_state_extends.
  destruct HS; constructor*; eapply wf_stat_state_extends; eauto.

(*proof of wf_ostringstat_state_extends*)
  introv Hext HS.
  clear wf_switchbody_state_extends wf_switchclause_state_extends wf_ostat_state_extends wf_ostringstat_state_extends wf_liststat_state_extends wf_listswitchclause_state_extends.
  destruct HS; constructor*; eapply wf_stat_state_extends; eauto.

(*proof of wf_liststat_state_extends*)
  introv Hext HS.
  clear wf_switchbody_state_extends wf_switchclause_state_extends wf_ostat_state_extends wf_ostringstat_state_extends wf_listswitchclause_state_extends.
  destruct HS; constructor*.

(*proof of wf_listswitchclause_state_extends*)
  introv Hext HS.
  clear wf_stat_state_extends wf_switchbody_state_extends wf_ostat_state_extends wf_ostringstat_state_extends wf_liststat_state_extends.
  destruct HS; constructor*.
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
  introv Hext HS. inverts HS ; constructor*. inverts Hext. unfolds in H0. unfolds.
  apply H0. apply H.
Qed.


Lemma wf_env_loc_state_extends : forall (S S':state) (str:strictness_flag) (L:env_loc),
  state_extends S' S ->
  wf_env_loc S str L ->
  wf_env_loc S' str L.
Proof.
  introv Hext HS. inverts HS. inverts* Hext. constructor*.
Qed.


Lemma wf_object_loc_state_extends : forall (S S':state) (str:strictness_flag) (l:object_loc),
  state_extends S' S ->
  wf_object_loc S str l ->
  wf_object_loc S' str l.
Proof.
  introv Hext HS. unfolds. unfolds. inverts* Hext.
Qed.


Lemma wf_decl_env_record_state_extends :  forall (S S':state) (str:strictness_flag) (d:decl_env_record),
  state_extends S' S ->
  wf_decl_env_record S str d ->
  wf_decl_env_record S' str d.
Proof.
  introv Hext HSd. unfolds wf_decl_env_record. introv H.
  forwards* M: HSd s m v. eapply wf_value_state_extends; eauto.
Qed.


Lemma wf_env_record_state_extends :  forall (S S':state) (str:strictness_flag) (E:env_record),
  state_extends S' S ->
  wf_env_record S str E ->
  wf_env_record S' str E.
Proof.
  introv Hext HSE. inverts* HSE; constructor*.
  eapply wf_decl_env_record_state_extends; eauto.
  eapply wf_object_loc_state_extends; eauto.
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
  inverts Hext. apply H. auto.
  inverts H0; constructor.
  inverts H; constructor.
  inverts Hext. apply H. auto.
  inverts H. unfolds in H0. inverts Hext. apply H1 in H0.
  constructor. auto.
Qed.

Lemma wf_res_state_extends : forall (S S':state) (str:strictness_flag) (R:res),
  state_extends S' S ->
  wf_res S str R ->
  wf_res S' str R.
Proof.
  introv Hext HS. inverts* HS. constructor*. apply* wf_resvalue_state_extends.
Qed.



Lemma wf_attributes_state_extends : forall (S S':state) (str:strictness_flag) (A:attributes),
  state_extends S' S ->
  wf_attributes S str A ->
  wf_attributes S' str A.
Proof.
  introv Hext HSA. inverts* HSA; constructor*; apply wf_value_state_extends with S; assumption.
Qed.


Lemma wf_descriptor_state_extends : forall (S S':state) (str:strictness_flag) (Desc:descriptor),
  state_extends S' S ->
  wf_descriptor S str Desc ->
  wf_descriptor S' str Desc.
Proof.
  introv Hext HSdesc. inverts* HSdesc. constructor*; clear ob1 ob2 ob3; inverts H; constructor*; eapply wf_value_state_extends; eauto.
Qed.


Lemma wf_object_state_extends : forall (S S':state) (str:strictness_flag) (obj:object),
  state_extends S' S ->
  wf_object S str obj ->
  wf_object S' str obj.
Proof.
  introv Hext HSobj. inverts HSobj; destruct obj; simpl in wf_object_proto_; simpl in wf_object_properties. constructor*; simpl; auto. eapply wf_value_state_extends; eauto.
  introv HA. eapply wf_attributes_state_extends; eauto.
Qed.


Lemma wf_lexical_env_state_extends : forall (S S':state) (str:strictness_flag) (lex:lexical_env),
  state_extends S' S ->
  wf_lexical_env S str lex ->
  wf_lexical_env S' str lex.
Proof.
  introv Hext HS. induction HS; constructor*. apply* wf_env_loc_state_extends. 
Qed.


Lemma wf_execution_ctx_state_extends : forall (S S':state) (str:strictness_flag) (C:execution_ctx),
  state_extends S' S ->
  wf_execution_ctx S str C ->
  wf_execution_ctx S' str C.
Proof.
  introv Hext HS. inverts HS; constructor*; solve [apply* wf_lexical_env_state_extends|apply* wf_lexical_env_state_extends|apply* wf_value_state_extends]. 
Qed.


Lemma wf_out_state_extends : forall (S S':state) (str:strictness_flag) (o:out),
  state_extends S S' ->(*it's a trap!*)
  wf_out S str o ->
  wf_out S' str o.
Proof.
  introv Hext Ho.
  destruct o; [inverts Ho | apply wf_out_ter]; inverts* Ho; eapply state_extends_trans; eauto.
Qed.


Lemma wf_specret_state_extends : forall (S S':state) (str:strictness_flag) (s:specret),
  state_extends S S' ->(*it's a trap!*)
  wf_specret S str s ->
  wf_specret S' str s.
Proof.
  introv Hext Hs.
  destruct s.
  inverts Hs; constructor*; apply* state_extends_trans.
  inverts Hs; constructor. apply* wf_out_state_extends. 
Qed.



(*lemmas: if x of type x is well-formed then out_of_X x is well-formed too*)

Lemma wf_out_of_specret_lem :  forall (S:state) (str:strictness_flag) (s:specret) (o:out),
  out_of_specret s = Some o ->
  wf_specret S str s ->
  wf_out S str o.
Proof.
  introv Ho Hs. inverts Hs; inverts* Ho.
Qed.


(*tactic to apply wf_out_of_specret_X*)
Ltac wf_out_of_specret :=
  match goal with
    | [ H:wf_specret ?S ?str ?s, H':out_of_specret ?s = Some ?o|- wf_out ?S ?str ?o ] =>
      apply* wf_out_of_specret_lem
  end.


Lemma wf_out_of_ext_expr : forall (S:state) (str:strictness_flag) (e:ext_expr) (o:out),
  out_of_ext_expr e = Some o ->
  wf_ext_expr S str e ->
  wf_out S str o.
Proof.
introv Ho He. inverts He; inverts* Ho; wf_out_of_specret.
Qed.


Lemma wf_out_of_ext_spec : forall (S:state) (str:strictness_flag) (e:ext_spec) (o:out),
  out_of_ext_spec e = Some o ->
  wf_ext_spec S str e ->
  wf_out S str o.
Proof.
introv Ho He. inverts He; inverts* Ho; wf_out_of_specret.
Qed.


Lemma wf_out_of_ext_stat : forall (S:state) (str:strictness_flag) (et:ext_stat) (o:out),
  out_of_ext_stat et = Some o ->
  wf_ext_stat S str et ->
  wf_out S str o.
Proof.
  introv Ho Het. inverts Het; inverts Ho; auto; try solve [wf_out_of_specret].
  destruct sv; inverts H1; inverts* H.
Qed.


Lemma wf_out_of_ext_prog : forall (S:state) (str:strictness_flag) (ep:ext_prog) (o:out),
  out_of_ext_prog ep = Some o ->
  wf_ext_prog S str ep ->
  wf_out S str o.
Proof.
  introv Ho Hep. 
  destruct ep; inverts Ho; inverts* Hep.
Qed.  




(*other lemmas*)

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


(*useful tactics to change the state*)
Ltac wf_out_change_state :=
  match goal with
    | [ H:state_extends ?S' ?S |- wf_out ?S _ _ ] =>
      apply wf_out_state_extends with S'; [apply H|]
  end.

Ltac wf_specret_change_state :=
  match goal with
    | [ H:state_extends ?S' ?S |- wf_specret ?S _ _ ] =>
      apply wf_specret_state_extends with S'; [apply H|]
  end.

Ltac wf_out_extends :=
  match goal with
    | [ H:state_extends ?S' ?S , H':wf_out ?S' ?str ?o |- wf_out ?S ?str ?o ] =>
      apply wf_out_state_extends with S'; [apply H|apply H']
  end.



Lemma eq_env_loc_dec : forall (L L':env_loc),
  {L = L'} + {L <> L'}.
Proof.
  introv.
  apply eq_nat_dec.
Qed.


Lemma heap_write_extends : forall {X Y:Type} (T T':Heap.heap X Y) (x:X) (y:Y),
  (forall (a b:X), {a=b}+{a<>b}) ->
  T' = Heap.write T x y ->
  heap_extends T' T.
Proof.
  introv Hd Hw. unfolds. introv HT. rewrite Heap.indom_equiv_binds.
  subst. forwards M: Hd x x0. inverts M.
  exists y. apply* @Heap.binds_write_eq.
  rewrite Heap.indom_equiv_binds in HT. inverts HT. exists x1. apply* @Heap.binds_write_neq.
Qed.


(*str doesn't matter for objects (for now)*)
Lemma wf_object_str : forall (str str0:strictness_flag) (S:state) (obj:object),
  wf_object S str obj ->
  wf_object S str0 obj.
Proof.
  introv Hstr. inverts Hstr; constructor*.
  (*wf_object_proto_*)
    inverts wf_object_proto_; constructor*.
  (*wf_object_properties*)
    clear wf_object_proto_. introv HA. forwards* M:wf_object_properties x A. clear wf_object_properties HA.
    inverts M; constructor*.
    inverts H; constructor*.
Qed.




(*lemmas about object_loc*)

Lemma eq_object_loc_dec : forall (l l':object_loc),
  {l = l'} + {l <> l'}.
Proof.
  introv.
  destruct l; destruct l'; try solve [ destruct p ; try (left; reflexivity); right; introv H'; inverts H'].
  forwards M:eq_nat_dec n n0; inverts M. left; reflexivity. right; introv H'; inverts H'; apply H; auto.
  destruct p; destruct p0; try solve [left; reflexivity| right; introv H'; inverts H'| left; destruct m; destruct m0; auto].
  destruct n; destruct n0; try solve [left; reflexivity | right; introv H'; inverts H'].
  destruct n; destruct n0; try solve [left; reflexivity | right; introv H'; inverts H'].
Qed.


Lemma object_binds_write_eq : forall (S:state) (l:object_loc) (o:object),
  object_binds (object_write S l o) l o.
Proof.
  introv. destruct S.  unfolds. simpl. apply Heap.binds_write_eq.
Qed.


Lemma object_binds_write_neq : forall (S:state) (l l':object_loc) (o o':object),
  object_binds S l o ->
  l <> l' ->  
  object_binds (object_write S l' o') l o.
Proof.
  introv Hl Hl'. unfolds; destruct S; simpl. apply Heap.binds_write_neq; auto.

Qed.


Lemma object_binds_write_inv : forall (S:state) (l l':object_loc) (o o':object),
  object_binds (object_write S l o) l' o' ->
  (l' = l /\ o' = o) \/ (l' <> l /\ object_binds S l' o').
Proof.
  introv Hl'. destruct S; unfolds in Hl'; simpl in Hl'.
  assert (H:(l' = l /\ o' = o) \/ (l' <> l /\ Heap.binds state_object_heap l' o')).
    apply Heap.binds_write_inv. auto.
  auto.
Qed.




(*important lemmas*)

Lemma wf_env_record_write : forall (str:strictness_flag) (S S':state) (E:env_record) (L:env_loc),
  wf_state S ->
  wf_env_record S str E ->
  S' = env_record_write S L E ->
  wf_state S' /\ state_extends S' S.
Proof.
  introv HS HS'. destruct S; subst; simpl.
  split. 
  (*wf_state*)
    inverts HS; simpl; simpl in wf_state_env_loc_global_env_record.
    inverts wf_state_prealloc_global. inverts H0; simpl in wf_state_prealloc_global_binds.
    constructor*.
    (*wf_state_wf_objects*)
      introv Hl. inverts Hl. forwards M: wf_state_wf_objects obj str. exists x0. unfolds object_binds; subst; simpl; simpl in H0; auto.
      clear wf_state_wf_objects HS' wf_state_wf_env_records.
      inverts M. constructor*. inverts wf_object_proto_; unfolds object_indom; subst; simpl; simpl in H2; constructor*.
      introv HA. forwards* M:wf_object_properties x1 A. inverts M; constructor*. inverts H1; subst; simpl; simpl in H0; constructor*.
      (*wf_state_prealloc_global*)
        exists x; constructor; subst; auto.
      (*wf_state_prealloc_native_error_proto*)
        unfolds object_indom; subst; simpl in wf_state_prealloc_native_error_proto; simpl; auto.
      (*wf_state_wf_env_records*)
        introv HL. inverts HL.
        clear wf_state_wf_objects wf_state_env_loc_global_env_record wf_state_prealloc_global_get wf_state_prealloc_global_get_own_prop wf_state_prealloc_global_binds wf_state_prealloc_global_define_own_prop x.
        forwards M:eq_env_loc_dec L x0. inverts M.
        (*L = x0*)
          clear wf_state_wf_env_records.
          unfolds env_record_binds. subst; simpl in H0. forwards M:@Heap.binds_write_inv H0.
          inverts M; inverts H; try solve [exfalso; auto]. clear H0 H1.
          inverts HS'; constructor*. unfolds; introv HH; forwards M:H HH; inverts M; constructors*.
        (*L <> x0*)
          clear HS'. subst. forwards M:wf_state_wf_env_records E0 str0.
          exists x0. unfolds env_record_binds; simpl; simpl in H0. apply Heap.binds_write_inv in H0; inverts H0; inverts H; try solve [exfalso; auto]; auto.
          clear wf_state_wf_env_records H1 H0 x0.
          inverts M; constructor*. unfolds wf_decl_env_record; simpl; simpl in H.
          introv HH. apply H in HH. inverts HH; constructor*.
      (*wf_state_env_loc_global_env_record*)
        subst; unfolds; simpl. rewrite Heap.dom_write. apply in_union_get_1. auto.
  (*state_extends*)
    clear HS HS'. subst; simpl; splits; try apply heap_extends_refl.
    simpl. unfolds. introv H. unfolds in H. unfolds. rewrite Heap.dom_write.
    apply in_union_get_1. auto.
Qed.  


Lemma wf_set_property : forall (S S':state) (str:strictness_flag) (l:object_loc) (x:prop_name) (A:attributes),
wf_state S ->
wf_attributes S str A ->
object_indom S l ->
object_set_property S l x A S' ->
wf_state S' /\ state_extends S' S.
Proof.
  introv HS HA Hl Hset.
  assert (Hext:state_extends S' S).
  (*state_extends (assert)*)
    clear HS HA. inverts Hset. destruct S; subst; simpl in H. inverts H.
    unfolds. split; simpl; try apply heap_extends_refl.
    unfolds. introv H1. clear Hl H0. unfolds. rewrite -> Heap.dom_write. unfolds in H1. apply in_union_get_1. auto.
  split.
  (*wf_state*)
    constructor*.
    (*wf_state_wf_objects*)
      introv Hobj. inverts Hset. inverts H. inverts Hobj.
      forwards M':eq_object_loc_dec l x1; inverts M'.
      (*l=x1*)
        forwards M:object_binds_write_inv H. inverts M; inverts H1; try solve [exfalso; apply H2; reflexivity]; clear H2.
        constructor*.
        (*wf_object_proto_*)
          unfolds object_map_properties; simpl. eapply wf_value_state_extends; eauto.
          inverts HS. clear H Hext wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record.
          forwards M:wf_state_wf_objects x0 str0. exists* x1.
          destruct x0; simpl; inverts M; auto.
        (*wf_object_define_own_prop*)
          unfolds object_map_properties; simpl. inverts HS. clear Hext wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record Hl. forwards M:wf_state_wf_objects x0 str. exists* x1.  inverts M; destruct x0; simpl in wf_object_define_own_prop; simpl; auto.
        (*wf_object_get_own_prop*)
          unfolds object_map_properties; simpl. inverts HS. clear Hext wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record Hl. forwards M:wf_state_wf_objects x0 str. exists* x1.  inverts M; destruct x0; simpl in wf_object_get_own_prop; simpl; auto.          
        (*wf_object_properties*)
          introv Hb. eapply wf_attributes_state_extends; eauto. clear Hext Hl. forwards M:string_dec x x2. inverts M.
          (*x=x2*)
            destruct x0; simpl in Hb;
            forwards M:(@Heap.binds_write_inv prop_name attributes) Hb; inverts M; inverts H1; try solve [exfalso; auto];
            inverts* HA; inverts* H1; rconstructors*.
          (*x<>x2*)
            inverts HS.
            forwards M:wf_state_wf_objects x0 str0. exists x1; auto.
            clear wf_state_wf_objects wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record H0 H x1.
            destruct x0; simpl in Hb;
            forwards M':(@Heap.binds_write_inv prop_name attributes) Hb; inverts M' ; inverts H; try solve [exfalso; auto]; clear H1 Hb H0.
            inverts M. simpl in wf_object_properties; forwards M:wf_object_properties x2 A0; auto.
      (*l<>x1*)
        forwards M:object_binds_write_inv H. inverts M; inverts H2; try solve [exfalso; apply H1; reflexivity]; clear H1 H3.
        unfolds object_map_properties; simpl.
        inverts HS. clear H wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record.
        forwards M:wf_state_wf_objects obj str0. exists* x1.
        eapply wf_object_state_extends; eauto.
    (*wf_state_prealloc_global*)
      inverts Hset. inverts H.
      assert (M:{l=prealloc_global}+{l<>prealloc_global}). apply eq_object_loc_dec.
      inverts M.
      (*l=prealloc_global*)
        exists (object_map_properties x0 (fun P : object_properties_type => Heap.write P x A)). constructor*;
        (*wf_state_prealloc_global_binds*)
            try (destruct S; subst; simpl; apply Heap.binds_write_eq);
        (*other cases*)
          inverts HS; simpl; inverts wf_state_prealloc_global; inverts H;
          assert (x0=x1); try (apply* Heap_binds_func; apply object_loc_comparable); subst;
          destruct x1; auto.
      (*l<>prealloc_global*)
        inverts HS. inverts wf_state_prealloc_global. exists x1. constructor*.
        destruct S; subst; simpl; apply Heap.binds_write_neq; auto.
        inverts H1; simpl in wf_state_prealloc_global_binds; auto.
    (*wf_state_prealloc_native_error_proto*)
        introv. inverts Hext. apply* H. inverts* HS. apply* wf_state_prealloc_native_error_proto.
    (*wf_state_wf_env_records*)
      introv HL.
      inverts HL. inverts HS. clear wf_state_wf_objects wf_state_prealloc_global wf_state_env_loc_global_env_record.
      eapply wf_env_record_state_extends; eauto. apply* wf_state_wf_env_records.
      exists x0. clear wf_state_wf_env_records Hext HA Hl.
      inverts Hset. inverts H0. destruct S; simpl in H. unfolds env_record_binds; auto.
    (*wf_state_env_record_heap*)
      inverts HS. inverts Hext. auto.
  (*state_extends*)
    auto.
Qed.


Lemma wf_env_record_write_decl_env : forall (S S':state) (str:strictness_flag) (L:env_loc) (x:prop_name) (mu:mutability) (v:value),
  wf_state S ->
  wf_env_loc S str L ->
  S' = env_record_write_decl_env S L x mu v ->
  wf_value S str v ->
  wf_state S' /\ state_extends S' S.
Proof.
  introv HS HL HS' Hv.
  assert (Hext:state_extends S' S).
  (*state_extends (assert)*)
    unfolds. unfolds env_record_write_decl_env. unfolds decl_env_record_write. destruct (Heap.read (state_env_record_heap S) L); subst; simpl. destruct S; subst; simpl. split. simpl. apply heap_extends_refl.
    unfolds. introv H. rewrite Heap.indom_equiv_binds. rewrite Heap.indom_equiv_binds in H. inverts H.
    assert (E:{L=x0} + {L<>x0}). apply eq_nat_dec. inverts E. eexists. apply Heap.binds_write_eq. eexists. eapply Heap.binds_write_neq; eauto.
    splits; apply heap_extends_refl.
  split.
  (*wf_state*)
    constructor*; inverts keep HS; subst.
    (*wf_state_wf_objects*)
      clear wf_state_prealloc_global wf_state_wf_env_records wf_state_env_loc_global_env_record.
      introv Hl. inverts Hl. eapply wf_object_state_extends; eauto.
      apply wf_state_wf_objects. clear wf_state_wf_objects Hv Hext.
      destruct S; simpl in H. unfolds env_record_write_decl_env. simpl in H.
      destruct (Heap.read state_env_record_heap L); subst; simpl; exists* x0.
    (*wf_state_prealloc_global*)
      clear wf_state_wf_objects wf_state_wf_env_records wf_state_env_loc_global_env_record Hext.
      inverts wf_state_prealloc_global. exists x0.
      inverts H; destruct S; simpl in wf_state_prealloc_global_binds; simpl in wf_state_prealloc_global_define_own_prop; simpl in wf_state_prealloc_global_get; simpl in wf_state_prealloc_global_get_own_prop.
      unfolds env_record_write_decl_env; simpl. constructor*; destruct (Heap.read state_env_record_heap L); simpl; auto.
    (*wf_state_prealloc_native_error_proto*)
      introv. inverts Hext. apply H. apply* wf_state_prealloc_native_error_proto.
    (*wf_state_wf_env_records*)
      clear wf_state_wf_objects wf_state_prealloc_global wf_state_env_loc_global_env_record.
      introv HL'. inverts HL'. forwards M:eq_env_loc_dec x0 L. inverts M.
      (*x0 = L*)
      forwards* M:wf_state_wf_env_records (Heap.read (state_env_record_heap S) L) str0. exists L. destruct S. simpl; unfolds; simpl. rewrite Heap.binds_equiv_read; auto. inverts* HL.
      clear wf_state_prealloc_native_error_proto.
      unfolds env_record_write_decl_env; simpl; simpl in H; simpl in Hext.
      inverts keep HL. simpl in H0; rewrite Heap.indom_equiv_binds in H0. inverts H0. 
      rewrite Heap.binds_equiv_read in H1; try solve [inverts* HL].
      subst.
      destruct (Heap.read (state_env_record_heap S) L). 
        (*env_record_decl*)
          destruct S.
          unfolds in H; simpl in H; apply Heap.binds_write_inv in H; inverts H; inverts H0; try solve [exfalso; auto]; clear H.
          constructor*. inverts M. unfolds. introv HH. eapply wf_value_state_extends; eauto. unfolds in HH. unfolds decl_env_record_write. apply Heap.binds_write_inv in HH.
          inverts HH.
          (*s = x*)
            inverts H. inverts H2. inverts Hv; rconstructors*.
          (*s <> x*)
            inverts H. unfolds wf_decl_env_record. apply* H0.
        (*env_record_object*)
          apply* wf_state_wf_env_records.
      (*x0 <> L*)
        eapply wf_env_record_state_extends; eauto.
        apply* wf_state_wf_env_records. exists x0. clear Hext wf_state_wf_env_records.
        destruct S. unfolds env_record_write_decl_env. simpl in H.
        destruct (Heap.read state_env_record_heap L).
        (*env_record_decl*)
          unfolds env_record_binds; simpl; simpl in H. apply Heap.binds_write_inv in H; inverts H; inverts H1; try solve [exfalso; auto]; auto.
        (*env_record_object*)
          auto.
    (*wf_state_env_loc_global_env_record*)
        clear wf_state_wf_objects wf_state_prealloc_global Hext.
      unfolds env_record_write_decl_env. destruct (Heap.read (state_env_record_heap S) L); simpl. unfolds env_record_write. unfolds state_map_env_record_heap. unfolds state_with_env_record_heap.
      destruct S; subst; simpl. simpl in wf_state_env_loc_global_env_record. unfolds.
      rewrite Heap.dom_write. apply in_union_get_1. unfolds in wf_state_env_loc_global_env_record. assumption.
      assumption.
  (*state_extends*)
    assumption.
Qed.


Lemma wf_state_wf_prealloc_global : forall (S:state) (str:strictness_flag),
  wf_state S ->
  wf_object_loc S str prealloc_global.
Proof.
  introv HS. inverts HS. unfolds. unfolds. rewrite Heap.indom_equiv_binds. inverts wf_state_prealloc_global. inverts H. exists* x.
Qed.


Lemma object_alloc_state_extends : forall (l:object_loc) (O:object) (S S':state),
  (l,S') = object_alloc S O ->
  state_extends S' S.
Proof.
  introv Hall. unfolds object_alloc. destruct S. destruct state_fresh_locations.
  unfolds. simpl. inverts Hall. simpl.
  split.
  apply* @heap_write_extends. apply eq_object_loc_dec.
  apply heap_extends_refl.
Qed.

    
Lemma wf_object_alloc : forall (str:strictness_flag) (l:object_loc) (O:object) (S S':state),
  (l,S') = object_alloc S O ->
  wf_state S ->
  wf_object S str O ->
  wf_state S' /\ wf_object_loc S' str l.
Proof.
  introv Hall. forwards* M:object_alloc_state_extends l O S S'.
  split.
  (*wf_state*)
  constructor*.
    (*wf_state_wf_objects*)
      introv Hobj. inverts Hobj. forwards E:eq_object_loc_dec x l. unfolds object_alloc. destruct S. destruct state_fresh_locations. inverts Hall.
      inverts E; unfolds object_binds; simpl in H1; apply Heap.binds_write_inv in H1.
      (*x=l*)
        clear H. inverts H1; try solve [inverts H; exfalso; auto]. inverts H; subst. clear H1.
        eapply wf_object_state_extends; eauto. apply wf_object_str with str; auto.
      (*x<>l*)
        clear H0. inverts H1; inverts H0; try solve [exfalso; auto]. clear H1 H2.
        eapply wf_object_state_extends; eauto. clear M. apply wf_object_str with str; auto. clear str0. inverts H. forwards* M:wf_state_wf_objects obj str.
    (*wf_state_prealloc_global*)
      inverts H. clear wf_state_wf_objects wf_state_wf_env_records wf_state_env_loc_global_env_record. inverts wf_state_prealloc_global. inverts H.
      unfolds object_alloc. destruct S. destruct state_fresh_locations. inverts Hall.  simpl in wf_state_prealloc_global_binds. simpl.
      assert (E:object_loc_normal n<>prealloc_global). introv H. inverts H.
      exists x. constructor*.
      (*wf_state_prealloc_global_binds*)
        clear M. apply* @Heap.binds_write_neq.
    (*wf_state_prealloc_native_error_proto*)
      introv. inverts M. apply* H1. inverts H. apply* wf_state_prealloc_native_error_proto.
    (*wf_state_wf_env_records*)
        clear H0. destruct S. unfolds object_alloc. destruct state_fresh_locations. inverts Hall. introv HH.
        inverts H. clear wf_state_wf_objects wf_state_prealloc_global wf_state_env_loc_global_env_record.
        unfolds env_record_binds. simpl. simpl in wf_state_wf_env_records. simpl in HH. eapply wf_state_wf_env_records in HH. eapply wf_env_record_state_extends; eauto.    
    (*wf_state_env_loc_global_env_record*)
      clear H0 M. unfolds object_alloc; destruct S; destruct state_fresh_locations; inverts Hall; simpl.
      inverts* H.
  (*wf_object_loc*)
    clear M H0 H. destruct S; destruct state_fresh_locations; inverts* Hall.
    unfolds. unfolds. rewrite Heap.indom_equiv_binds.
    simpl. exists O. apply* @Heap.binds_write_eq.
Qed.


Lemma wf_decl_env_record_rem : forall (S:state) (str:strictness_flag) (Ed:decl_env_record) (x:prop_name),
  wf_decl_env_record S str Ed ->
  wf_decl_env_record S str (decl_env_record_rem Ed x).
Proof.
  introv Hed. unfolds. introv Hb. unfolds decl_env_record_rem. unfolds decl_env_record_binds.
  apply Heap.binds_rem_inv in Hb. inverts Hb.
  unfolds wf_decl_env_record. unfolds decl_env_record_binds.
  apply* Hed.
Qed.


Lemma object_write_state_extends : forall (S:state) (O:object) (l:object_loc),
  state_extends (object_write S l O) S.
Proof.
  introv. unfolds. destruct S; split; simpl; [apply* @heap_write_extends; apply* eq_object_loc_dec | apply heap_extends_refl].
Qed.


Lemma object_rem_property_state_extends : forall (S S':state) (l:object_loc) (x:prop_name),
  object_rem_property S l x S' ->
  state_extends S' S.
Proof.
  introv Hr. unfolds in Hr. unfolds in Hr. inverts Hr. inverts H.
  apply object_write_state_extends.
Qed.

(*
Lemma wf_object_write : forall (S:state) (str:strictness_flag) (l:object_loc) (O:object),
  wf_state S ->
  wf_object S str O ->
  wf_state (object_write S l O).
Proof.
  introv HS HO. forwards M:object_write_state_extends S O l. constructor*.
  (*wf_state_wf_objects*)
    introv Hl. apply* wf_object_state_extends. apply wf_object_str with str. inverts Hl. apply object_binds_write_inv in H. inverts H; inverts* H0.
    (*x <> l*)
      inverts HS. apply* wf_state_wf_objects.
  (*wf_state_prealloc_global*)
    inverts HS. inverts wf_state_prealloc_global. exists x. inverts H.
    constructor*.
    
  (*wf_state_prealloc_native_error_proto*)
  (*wf_state_wf_env_records*)
  (*wf_state_env_loc_global_env_record*)
*)

Lemma wf_object_rem_property : forall (S S':state) (l:object_loc) (x:prop_name),
  wf_state S ->
  object_rem_property S l x S' ->
  wf_state S'.
Proof.
  introv HS Hr. forwards M:object_rem_property_state_extends Hr. unfolds in Hr; unfolds in Hr; inverts Hr; inverts H. constructor*.
  (*wf_state_wf_objects*)
    introv Hl. inverts Hl. apply* wf_object_state_extends. clear M. apply object_binds_write_inv in H. inverts H; inverts* H1.
    (*x = l*)
      inverts HS. forwards* M:wf_state_wf_objects x0 str.
      unfolds object_map_properties. destruct x0. inverts M. simpl.
      rconstructors*; simpl.
      simpl in wf_object_properties. introv HH. apply Heap.binds_rem_inv in HH. inverts* HH.
    (*x <> l*)
      inverts HS. apply* wf_state_wf_objects.
  (*wf_state_prealloc_global*)
    inverts HS. forwards MM:eq_object_loc_dec l prealloc_global. inverts MM.
    (*l = prealloc_global*)
      clear M wf_state_wf_objects wf_state_prealloc_native_error_proto wf_state_wf_env_records wf_state_env_loc_global_env_record.
      inverts wf_state_prealloc_global. inverts H. forwards* M:Heap_binds_func H0 wf_state_prealloc_global_binds. apply object_loc_comparable. subst.
      clear H0.      
      eexists; constructor; try (destruct S; simpl; apply* @Heap.binds_write_eq);
      destruct x1; simpl; simpl in wf_state_prealloc_global_define_own_prop; simpl in wf_state_prealloc_global_get; simpl in wf_state_prealloc_global_get; simpl in wf_state_prealloc_global_get_own_prop; subst; auto.
    (*l <> prealloc_global*)
      inverts wf_state_prealloc_global. exists x1. inverts H1; constructor*.
      destruct S. simpl. apply* @Heap.binds_write_neq.
  (*wf_state_prealloc_native_error_proto*)
    introv. apply M. inverts* HS. apply* wf_state_prealloc_native_error_proto.      
  (*wf_state_wf_env_records*)
    introv HL. apply* wf_env_record_state_extends. inverts HL; inverts HS; destruct S.
    apply* wf_state_wf_env_records.
  (*wf_state_env_loc_global_env_record*)
    apply* M. inverts* HS.
Qed.



(*lemmas: the initial state and execution_ctx are well-formed*)

(*record: the objects in the initial state are well-formed*)
Record wf_state_initial_wf_objects_aux (S:state) (str:strictness_flag):=
  {wf_initial_object_prealloc_global : wf_object S str object_prealloc_global;
   wf_initial_object_prealloc_object : wf_object S str object_prealloc_object;
   wf_initial_object_prealloc_object_proto : wf_object S str object_prealloc_object_proto;
   wf_initial_object_prealloc_bool : wf_object S str object_prealloc_bool;
   wf_initial_object_prealloc_bool_proto : wf_object S str object_prealloc_bool_proto;
   wf_initial_object_prealloc_numbe : wf_object S str object_prealloc_number;
   wf_initial_object_prealloc_number_proto : wf_object S str object_prealloc_number_proto;
   wf_initial_object_prealloc_function : wf_object S str object_prealloc_function;
   wf_initial_object_prealloc_function_proto  : wf_object S str object_prealloc_function_proto ;
   wf_initial_object_prealloc_array : wf_object S str object_prealloc_array;
   wf_initial_object_prealloc_array_proto : wf_object S str object_prealloc_array_proto;
   wf_initial_object_prealloc_string : wf_object S str object_prealloc_string;
   wf_initial_object_prealloc_string_proto : wf_object S str object_prealloc_string_proto;
   wf_initial_object_prealloc_error_proto : wf_object S str object_prealloc_error_proto;
   wf_initial_object_prealloc_native_error_proto_native_error_eval : wf_object S str (object_prealloc_native_error_proto native_error_eval);
   wf_initial_object_prealloc_native_error_proto_native_error_range : wf_object S str (object_prealloc_native_error_proto native_error_range);
   wf_initial_object_prealloc_native_error_proto_native_error_ref : wf_object S str (object_prealloc_native_error_proto native_error_ref);
   wf_initial_object_prealloc_native_error_proto_native_error_syntax : wf_object S str (object_prealloc_native_error_proto native_error_syntax);
   wf_initial_object_prealloc_native_error_proto_native_error_type : wf_object S str (object_prealloc_native_error_proto native_error_type);
   wf_initial_object_prealloc_error : wf_object S str (object_prealloc_error);
   wf_initial_object_prealloc_native_error_native_error_eval : wf_object S str (object_prealloc_native_error native_error_eval);
   wf_initial_object_prealloc_native_error_native_error_range : wf_object S str (object_prealloc_native_error native_error_range);
   wf_initial_object_prealloc_native_error_native_error_ref : wf_object S str (object_prealloc_native_error native_error_ref);
   wf_initial_object_prealloc_native_error_native_error_syntax : wf_object S str (object_prealloc_native_error native_error_syntax);
   wf_initial_object_prealloc_native_error_native_error_type : wf_object S str (object_prealloc_native_error native_error_type);
   wf_initial_throw_type_error_object : wf_object S str throw_type_error_object;
   wf_initial_global_eval_function_object : wf_object S str global_eval_function_object;
   wf_initial_global_is_nan_function_object : wf_object S str global_is_nan_function_object;
   wf_initial_global_is_finite_function_object : wf_object S str global_is_finite_function_object;
   wf_initial_object_get_proto_of_function_object : wf_object S str object_get_proto_of_function_object;
   wf_initial_object_get_own_prop_descriptor_function_object : wf_object S str object_get_own_prop_descriptor_function_object;
   wf_initial_object_get_own_prop_name_function_object : wf_object S str object_get_own_prop_name_function_object;
   wf_initial_object_create_function_object : wf_object S str object_create_function_object;
   wf_initial_object_define_prop_function_object : wf_object S str object_define_prop_function_object;
   wf_initial_object_define_props_function_object : wf_object S str object_define_props_function_object;
   wf_initial_object_seal_function_object : wf_object S str object_seal_function_object;
   wf_initial_object_freeze_function_object : wf_object S str object_freeze_function_object;
   wf_initial_object_prevent_extensions_function_object : wf_object S str object_prevent_extensions_function_object;
   wf_initial_object_is_sealed_function_object : wf_object S str object_is_sealed_function_object;
   wf_initial_object_is_frozen_function_object : wf_object S str object_is_frozen_function_object;
   wf_initial_object_is_extensible_function_object : wf_object S str object_is_extensible_function_object;
   wf_initial_object_proto_to_string_function_object : wf_object S str object_proto_to_string_function_object;
   wf_initial_object_proto_value_of_function_object : wf_object S str object_proto_value_of_function_object;
   wf_initial_object_proto_has_own_prop_function_object : wf_object S str object_proto_has_own_prop_function_object;
   wf_initial_object_proto_is_prototype_of_function_object : wf_object S str object_proto_is_prototype_of_function_object;
   wf_initial_object_proto_prop_is_enumerable_function_object : wf_object S str object_proto_prop_is_enumerable_function_object;
   wf_initial_array_proto_pop_function_object : wf_object S str array_proto_pop_function_object;
   wf_initial_array_proto_push_function_object : wf_object S str array_proto_push_function_object;
   wf_initial_string_proto_to_string_function_object : wf_object S str string_proto_to_string_function_object;
   wf_initial_string_proto_value_of_function_object : wf_object S str string_proto_value_of_function_object;
   wf_initial_bool_proto_to_string_function_object : wf_object S str bool_proto_to_string_function_object;
   wf_initial_bool_proto_value_of_function_object : wf_object S str bool_proto_value_of_function_object;
   wf_initial_number_proto_to_string_function_object : wf_object S str number_proto_to_string_function_object;
   wf_initial_number_proto_value_of_function_object : wf_object S str number_proto_value_of_function_object;
   wf_initial_error_proto_to_string_function_object : wf_object S str error_proto_to_string_function_object}.




Lemma heap_empty_binds_false : forall {X Y:Type} (x:X) (y:Y),
  Heap.binds Heap.empty x y ->
  False.
Proof.
  introv Hb.
  assert (M: exists (y':Y), Heap.binds Heap.empty x y'); [exists* y|].
  rewrite <- Heap.indom_equiv_binds in M. unfolds in M. rewrite Heap.dom_empty in M.
  inverts M.
Qed.  


(*tactic to find something in a heap*)
Ltac find_in_heap :=
  match goal with
    | [|-Heap.binds _ _ _] => let h := fresh in
      repeat (try (apply Heap.binds_write_eq; reflexivity); (apply Heap.binds_write_neq; [|introv h; inverts h]))
    | [|-exists _, Heap.binds _ _ _] => eexists;
      (let h := fresh in
        repeat (try (apply Heap.binds_write_eq; reflexivity); (apply Heap.binds_write_neq; [|introv h; inverts h])))
    | [|-Heap.indom _ _] => rewrite Heap.indom_equiv_binds; eexists;
      (let h := fresh in
        repeat (try (apply Heap.binds_write_eq; reflexivity); (apply Heap.binds_write_neq; [|introv h; inverts h])))
  end.


Lemma wf_initial_objects : forall (str:strictness_flag),
  wf_value state_initial str object_prealloc_global_proto ->
  wf_state_initial_wf_objects_aux state_initial str.
Proof.
  introv Hwf1.
  (*first show that some object_locs are well-formed*)
  assert (Hwf2:wf_value state_initial str prealloc_object_proto).
    constructor. unfolds. simpl. rewrite Heap.indom_equiv_binds.
    exists object_prealloc_object_proto.
    find_in_heap.
  assert (Hwf3:wf_value state_initial str prealloc_function_proto). 
    constructor. unfolds. simpl. rewrite Heap.indom_equiv_binds.
    exists object_prealloc_function_proto.
    find_in_heap.
  assert (Hwf4:wf_value state_initial str prealloc_error_proto).
    constructor. unfolds. simpl. rewrite Heap.indom_equiv_binds.
    exists object_prealloc_error_proto.
    find_in_heap.
  (*now, the theorem*)
  constructor*;(*now the goals are the wf_object*)
  (constructor;(*now the goals are the wf_object_proto_, wf_object_define_own_prop and wf_object_properties*)
    [simpl; solve [constructor*|auto] (*proves the wf_object_proto_*)
    |auto (*proves the wf_object_define_own_prop*)
    |auto (*proves the wf_object_get_own_prop*)
    |introv Hb; (*the goal is now wf_attributes*)
      (*find every property in the heap*)
      repeat (simpl in Hb; apply Heap.binds_write_inv in Hb; inverts Hb;
        [inverts H; constructor; constructor; unfolds; find_in_heap
        | inverts H; clear H0; rename H1  into Hb]);
      exfalso; apply* @heap_empty_binds_false]).  
Qed.


Theorem wf_state_initial :
  (forall (str:strictness_flag), wf_value state_initial str object_prealloc_global_proto) ->
  wf_state state_initial.
Proof.
  introv Hwf.
  constructor.
  (*wf_state_wf_objects*)
    introv Hb. inverts Hb.
    forwards* M:wf_initial_objects str.
    (*unfold everything*)
    unfold state_initial in H. unfolds in H. simpl in H.
    unfolds object_heap_initial; unfolds object_heap_initial_function_objects;
    unfolds object_heap_initial_function_objects_3;
    unfolds object_heap_initial_function_objects_2;
    unfolds object_heap_initial_function_objects_1.
    (*apply the lemma*)
    repeat (apply Heap.binds_write_inv in H; inverts H; inverts H0;
      [inverts* M | clear H; rename H1 into H]).
    (*now the heap is empty*)
    exfalso; apply* @heap_empty_binds_false.
  (*wf_state_prealloc_global*)
    exists object_prealloc_global. constructor*.
    find_in_heap.
  (*wf_state_prealloc_native_error_proto*)
    introv. unfolds; simpl; rewrite Heap.indom_equiv_binds.
    exists (object_prealloc_native_error_proto ne).
    destruct ne;
    find_in_heap.
  (*wf_state_wf_env_records*)
    introv Hb. inverts Hb. unfolds env_record_binds; simpl in H.
    apply Heap.binds_write_inv in H. inverts H.
    inverts H0. constructor*. unfolds. unfolds. rewrite Heap.indom_equiv_binds.
    exists object_prealloc_global.
    find_in_heap.
    inverts H0; exfalso; apply* @heap_empty_binds_false.
  (*wf_state_env_loc_global_env_records*)
    rewrite Heap.indom_equiv_binds.
    exists (env_record_object_default prealloc_global). apply Heap.binds_write_eq.
Qed.



Theorem wf_execution_ctx_initial : forall (str:strictness_flag),
  wf_execution_ctx state_initial str (execution_ctx_initial str).
Proof.
  introv. constructor*.
  rconstructors*. find_in_heap.
  rconstructors*. find_in_heap.
  simpl. constructor*. unfolds. find_in_heap.
Qed.





(*tactics used in the proof of pr_red_spec and pr_red_ext_expr*)
Ltac wf_impossible_aux :=
match goal with
  | [ H:wf_expr _ _ _ |- _ ] => inversion H; subst
  | [ H:wf_ext_expr _ _ _ |- _ ] => inversion H; subst
end.

Ltac wf_impossible :=
  try solve [wf_impossible_aux;wf_impossible_aux].

Ltac wf_impossible_spec_aux :=
match goal with
  | [ H:wf_ext_spec _ _ _ |- _ ] => inversion H; subst
end.

Ltac wf_impossible_spec :=
  try solve [wf_impossible_spec_aux].


Ltac wf_inverts :=
  match goal with
    | [H:wf_out _ _ (out_ter _ _)|-_] => inverts H
    | [H:wf_out _ _ (out_void _)|-_] => inverts H
    | [H:wf_specret _ _ (ret _ _)|-_] => inverts H
    | [H:wf_specret _ _ (dret _ _)|-_] => inverts H
    | [H:wf_specret _ _ (vret _ _)|-_] => inverts H
    | [H:wf_specret _ _ specval_void|-_] => clear H
    | [H:wf_specval _ _ (specval_value _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_value2 _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_int _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_ref _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_full_descriptor _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_attributes _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_descriptor _)|-_] => inverts H
    | [H:wf_specval _ _ (specval_listvalue _)|-_] => inverts H
    | [H:wf_full_descriptor _ _ full_descriptor_undef|-_] => clear H
    | [H:wf_full_descriptor _ _ (full_descriptor_some _)|-_] => inverts H
    | [H:wf_ext_expr _ _ _|-_] => inverts H
    | [H:wf_ext_spec _ _ _ |-_] => inverts H
    | [H:wf_obinary_op (Some _) |-_] => inverts H
    | [H:wf_obinary_op None |-_] => clear H
    | [H:wf_ovalue _ _ (Some _) |-_] => inverts H
    | [H:wf_ovalue _ _ None |-_] => clear H
    | [H:wf_env_record _ _ (env_record_object _ _) |-_] => inverts H
    | [H:wf_resvalue _ _ (resvalue_value _) |- _] => inverts H
    | [H:wf_resvalue _ _ (resvalue_ref _) |- _] => inverts H
    | [H:wf_res _ _ (res_intro _ _ _) |- _] => inverts H
    | [H:wf_res _ _ (res_normal _) |- _] => inverts H
    | [H:wf_res _ _ (res_ref _) |- _] => inverts H
    | [H:wf_res _ _ (res_val _) |- _] => inverts H
    | [H:wf_ref _ _ (ref_intro _ _ _) |- _] => inverts H
    | [H:wf_ref_base_type _ _ (ref_base_type_value _) |- _]=> inverts H
    | [H:wf_ref_base_type _ _ (ref_base_type_env_loc _) |- _]=> inverts H
    | [H:wf_descriptor _ _ (descriptor_intro _ _ _ _ _ _)|-_] => inverts H
    | [H:wf_attributes _ _ (attributes_data_of (attributes_data_intro _ _ _ _))|-_] => inverts H
    | [H:wf_oattributes _ _ None|-_] => clear H
    | [H:wf_oattributes _ _ (Some _)|-_] => inverts H
    | [H:wf_value _ _ (value_object _)|-_] => inverts H
    | [H:wf_value _ _ (value_prim _)|-_] => inverts H
    | [H:wf_oexpr _ _ None|-_] => clear H
    | [H:wf_oexpr _ _ (Some _) |-_] => inverts H
    | [H:wf_ostat _ _ None |-_] => clear H
    | [H:wf_ostat _ _ (Some _) |-_] => inverts H
    | [H:wf_ostringstat _ _ None |-_] => clear H
    | [H:wf_ostringstat _ _ (Some _) |-_] => inverts H
  end.

Ltac wf_inverts3a :=
  try (wf_inverts; try (wf_inverts; try wf_inverts)); auto.



Ltac wf_state_extends :=
  match goal with
    | [H:state_extends ?S ?S', H':wf_expr ?S' ?str ?e |- wf_expr ?S ?str ?e] => forwards M: wf_expr_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_value ?S' ?str ?v |- wf_value ?S ?str ?v] => forwards M: wf_value_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_resvalue ?S' ?str ?rv |- wf_resvalue ?S ?str ?rv] => forwards M: wf_resvalue_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_ref ?S' ?str ?rv |- wf_ref ?S ?str ?rv] => forwards M: wf_ref_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_attributes ?S' ?str ?rv |- wf_attributes ?S ?str ?rv] => forwards M: wf_attributes_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_descriptor ?S' ?str ?rv |- wf_descriptor ?S ?str ?rv] => forwards M: wf_descriptor_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_prog ?S' ?str ?rv |- wf_prog ?S ?str ?rv] => forwards M: wf_prog_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_object_loc ?S' ?str ?l |- wf_object_loc ?S ?str ?l] => forwards M: wf_object_loc_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_execution_ctx ?S' ?str ?C |- wf_execution_ctx ?S ?str ?C] => forwards M: wf_execution_ctx_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_env_loc ?S' ?str ?C |- wf_env_loc ?S ?str ?C] => forwards M: wf_env_loc_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_lexical_env ?S' ?str ?C |- wf_lexical_env ?S ?str ?C] => forwards M: wf_lexical_env_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_stat ?S' ?str ?t |- wf_stat ?S ?str ?t] => forwards M: wf_stat_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_switchbody ?S' ?str ?sb |- wf_switchbody ?S ?str ?sb] => forwards M: wf_switchbody_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_switchclause ?S' ?str ?sc |- wf_switchclause ?S ?str ?sc] => forwards M: wf_switchclause_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_liststat ?S' ?str ?lt |- wf_liststat ?S ?str ?lt] => forwards M: wf_liststat_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_listswitchclause ?S' ?str ?lsc |- wf_listswitchclause ?S ?str ?lsc] => forwards M: wf_listswitchclause_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_oexpr ?S' ?str ?oe |- wf_oexpr ?S ?str ?oe] => forwards M: wf_oexpr_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_ostat ?S' ?str ?ot |- wf_ostat ?S ?str ?ot] => forwards M: wf_ostat_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_ostringstat ?S' ?str ?ost |- wf_ostringstat ?S ?str ?ost] => forwards M: wf_ostringstat_state_extends H H'; assumption
    | [H:state_extends ?S ?S', H':wf_res ?S' ?str ?R |- wf_res ?S ?str ?R] => forwards M: wf_res_state_extends H H'; assumption
                                                                                                                       
  end.


Ltac appred :=
  match goal with
    |[H:(forall _ _ _ _  _, wf_state _ -> wf_execution_ctx _ _ _ -> wf_ext_spec _ _ _ -> red_spec _ _ _ _ -> wf_specret _ _ _), HH:red_spec ?S ?C ?es ?y |- wf_specret ?S _ ?y] => apply* H
    |[H:(forall _ _ _ _  _, red_expr _ _ _ _ -> wf_state _ -> wf_execution_ctx _ _ _ -> wf_ext_expr _ _ _ -> wf_out _ _ _), HH:red_expr ?S ?C ?es ?y |- wf_out ?S _ ?o] => apply* H
  end.
 

Hint Resolve state_extends_refl : core.
Hint Extern 0 (wf_out _ _ _) => wf_out_extends : core.
Hint Extern 0 => wf_state_extends : core.
Hint Extern 0 => appred : core.

Hint Resolve state_extends_refl : wf_base.
Hint Extern 0 (wf_out _ _ _) => wf_out_extends : wf_base.
Hint Extern 0 (wf_out _ _ _) => wf_out_change_state : wf_base.
Hint Extern 1 => constructor : wf_base.
Hint Extern 0 => wf_inverts : wf_base.
Hint Extern 1 => wf_inverts3a : wf_base.
Hint Extern 0 => wf_state_extends : wf_base.
Hint Resolve wf_state_wf_prealloc_global : wf_base.

Hint Extern 0 => appred : wf_base.

Hint Constructors Forall wf_expr wf_prog wf_stat wf_var_decl wf_ext_expr wf_ext_stat wf_ext_prog state_of_out wf_ext_spec wf_res wf_full_descriptor wf_specret wf_specval : wf_base.


(*Theorems: wf is preserved by reduction*)

Theorem pr_red_spec : forall (S:state) (C:execution_ctx) (str:strictness_flag) (es:ext_spec) (s:specret),
  wf_state S ->
  wf_execution_ctx S str C ->
  wf_ext_spec S str es ->
  red_spec S C es s ->
  wf_specret S str s

with pr_red_expr : forall (S:state) (C:execution_ctx) (ee:ext_expr) (o:out) (str:strictness_flag),
  red_expr S C ee o ->
  wf_state S ->
  wf_execution_ctx S str C ->
  wf_ext_expr S str ee ->
  wf_out S str o.
Proof.
(*proof of pr_red_spec*)
 introv HS HC Hes Hred. destruct Hred; wf_impossible_spec; auto.
 
  (*red_spec_abort*)
  constructor* ; apply* wf_out_of_ext_spec.

  (*red_spec_to_int32*)
  wf_inverts3a. apply* pr_red_spec. constructor*.

  wf_inverts3a. rconstructors*.

  (*red_spec_to_uint32*)
  wf_inverts3a. apply* pr_red_spec. constructor*.

  wf_inverts3a. rconstructors*.

  (*red_spec_converts_twice*)
  wf_inverts; apply* pr_red_spec; (forwards* M:pr_red_expr o1 str; try constructor* ); inverts M;
  econstructor; eauto; rconstructors*; wf_state_extends.

  wf_inverts. wf_inverts. inverts H3. inverts H7. inverts H8. wf_specret_change_state. apply* pr_red_spec. wf_state_extends. constructor*.

  wf_inverts3a. auto with wf_base.

  (*red_spec_expr_get_value_conv*)
  wf_inverts. apply* pr_red_spec. constructor*. apply* pr_red_spec. constructor*.
  
  wf_inverts3a. apply* pr_red_spec. constructor*. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a. wf_inverts. rconstructors*.

  (*spec_object_get_own_prop*)
  wf_inverts3a. apply* pr_red_spec. clear Hred.
  unfolds object_method. inverts H. inverts H0.
  inverts HS; clear wf_state_prealloc_global wf_state_prealloc_native_error_proto wf_state_wf_env_records wf_state_env_loc_global_env_record.
  forwards* M:wf_state_wf_objects x0 str. clear wf_state_wf_objects.
  inverts M. rewrite wf_object_get_own_prop. constructor*.

  wf_inverts3a. apply* pr_red_spec. constructor*.
  unfolds object_property. inverts H. unfolds object_method. inverts H0.
  inverts H. inverts H0.
  inverts HS; clear wf_state_prealloc_global wf_state_prealloc_native_error_proto wf_state_wf_env_records wf_state_env_loc_global_env_record.
  forwards* M:wf_state_wf_objects x1 str. clear wf_state_wf_objects.
  inverts M. clear wf_object_proto_ wf_object_define_own_prop wf_object_get_own_prop.
  destruct (Heap.read_option (object_properties_ x1) x) eqn:M; constructor*.
  rewrite <- Heap.binds_equiv_read_option in M. apply* wf_object_properties.

  rconstructors*.

  wf_inverts3a. rconstructors*.

  (*red_spec_ref_get_value*)
  wf_inverts3a. rconstructors*.

  wf_inverts3a. apply* pr_red_spec. constructor*.

  wf_inverts3a. apply* pr_red_spec. constructor*. apply* pr_red_expr. destruct r. simpl in H0. inverts H5. subst. inverts H4. cases_if; subst; rconstructors*.

  wf_inverts3a. wf_inverts3a. rconstructors*.

  wf_inverts3a. apply* pr_red_spec. rconstructors*. 

  wf_inverts3a. wf_inverts3a. rconstructors*.

  (*red_spec_expr_get_value*)
  wf_inverts3a. apply* pr_red_spec. constructor*. 

  wf_inverts3a. wf_specret_change_state. apply* pr_red_spec. wf_state_extends. auto with wf_base.

  (*red_spec_lexical_env_get_identifier_ref*)
  wf_inverts3a.  subst; rconstructors*. 

  wf_inverts3a. apply* pr_red_spec. inverts H0. constructor*. 


  wf_inverts3a. apply* pr_red_spec. constructors*.

  wf_inverts3a. rconstructors*. subst; unfolds ref_create_env_loc. constructor*. constructor. wf_state_extends.

  wf_inverts3a. wf_specret_change_state. apply* pr_red_spec; auto with wf_base.

  (*red_spec_error_spec*)
  wf_inverts3a. apply* pr_red_spec. constructor*.

  (*red_spec_object_get_prop*)
  wf_inverts3a. destruct B. apply* pr_red_spec. auto with wf_base.

  wf_inverts3a. apply* pr_red_spec. constructor*. apply* pr_red_spec. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_specret_change_state. apply* pr_red_spec; auto with wf_base. constructor*; auto with wf_base. inverts H3. inverts H. inverts H0. unfolds object_binds.
  forwards M:wf_state_wf_objects x0 str. exists* l. inverts M.
  auto.

  auto with wf_base.

  wf_inverts3a. apply* pr_red_spec. constructor*.



(*proof of pr_red_expr*)
  introv Hred HS HC Hee. destruct Hred; auto.

  apply* wf_out_of_ext_expr.

  subst; rconstructors*; inverts* HC.

  apply* pr_red_expr. constructor*. apply* pr_red_spec. constructor*. apply* HC.

  wf_inverts3a. repeat constructor*.
  
  wf_inverts3a. constructor*. subst. repeat constructor.

  apply* pr_red_expr. constructor. apply* pr_red_expr. constructor.  wf_inverts. inverts H1. assumption.
  
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr; rconstructors*. apply* pr_red_spec; auto with wf_base.

  wf_inverts3a. inverts H1. wf_out_change_state. apply* pr_red_expr; rconstructors*. auto with wf_base.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. auto with wf_base. constructors. cases_if; subst; constructor. apply* pr_red_expr.

  wf_inverts3a. repeat constructor*.

  wf_inverts. inverts H2. apply* pr_red_expr. constructor. apply* pr_red_spec. constructor*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts. inverts H0. apply* pr_red_expr.

  wf_inverts3a; rconstructors*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. auto with wf_base.

  rconstructors*.

  wf_inverts3a. wf_out_change_state. wf_inverts. destruct r; subst; simpl in H0; subst; inverts H2. apply* pr_red_expr; constructor*; auto with wf_base. 

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. auto with wf_base.

  wf_inverts3a. wf_inverts. destruct r; subst; inverts H; subst; simpl in H0; subst; inverts H1.  auto with wf_base.

  wf_inverts3a.

  constructor*. repeat constructor.
  
  wf_inverts. inverts H0. apply* pr_red_expr.

  wf_inverts3a. wf_out_change_state. auto with wf_base.

  wf_inverts3a. constructor*. repeat constructor.
  
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. auto with wf_base.
  
  wf_inverts3a. constructor*. repeat constructor. 

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a. constructor*. repeat constructor.

  wf_inverts3a. apply* pr_red_expr. constructor. apply* pr_red_spec. constructor~.

  auto with wf_base.

  auto with wf_base.

  auto with wf_base.

  wf_inverts3a. apply* pr_red_expr. inverts H2. auto with wf_base.

  (*red_expr_binary_op_1*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_spec; auto. constructor*.
  
  (*red_expr_binary_op_2*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  (*red_expr_binary_op_add*)
  wf_inverts. apply* pr_red_expr. constructor. apply* pr_red_spec. rconstructors*.

  (*red_expr_binary_op_add_1_string*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor. apply* pr_red_spec; auto. rconstructors*.

  (*red_expr_binary_op_add_string_1*)
  wf_inverts3a. rconstructors*.

  (*red_expr_binary_op_add_1_number*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_spec. wf_state_extends. rconstructors*.

  (*red_expr_puremath_op*)
  wf_inverts. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. rconstructors*.

  (*red_expr_puremath_op_1*)
  wf_inverts3a. wf_out_change_state. rconstructors*.
  
  (*red_expr_shift_op*)
  wf_inverts3a. apply* pr_red_expr. constructor*. apply* pr_red_spec. cases_if; subst; constructor*.

  (*red_expr_shift_op_1*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_spec. auto. constructor*.

  (*red_expr_shift_op_2*)
  wf_inverts3a. rconstructors*.

  (*red_expr_inequality_op*)
  wf_inverts3a.

  (*red_expr_inequality_op_1*)
  wf_inverts3a. apply* pr_red_expr. constructor*. apply* pr_red_spec. rconstructors*.

  (*red_expr_inequality_op_2*)
  wf_inverts3a. rconstructors*.

  (*red_expr_binary_op_instanceof_normal*)
  wf_inverts3a. auto with wf_base.

  (*red_expr_binary_op_in_object*)
  wf_inverts3a. auto with wf_base.

  (*red_expr_binary_op_equal*)
  wf_inverts3a.

  (*red_expr_binary_op_disequal*)
  wf_inverts3a.

  (*red_expr_binary_op_disequal_1*)
  wf_inverts3a. auto with wf_base.

  (*red_spec_equal*)
  wf_inverts3a.

  (*red_spec_equal_1_same_type*)
  wf_inverts3a. auto with wf_base.

  (*red_spec_equal_1_diff_type*)
  repeat  (cases_if; [wf_inverts3a; apply* pr_red_expr; subst; auto with wf_base|]).
  wf_inverts3a; apply* pr_red_expr; subst; auto with wf_base.

  (*red_spec_equal_2_return*)
  wf_inverts3a. rconstructors*.

  (*red_spec_equal_3_convert_and_recurse*)
  wf_inverts. apply* pr_red_expr.

  (*red_spec_equal_4_recurse*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. wf_inverts. rconstructors*.

  (*red_expr_binary_op_strict_equal*)
  wf_inverts3a. rconstructors*.

  (*red_expr_binary_op_strict_disequal*)
  wf_inverts3a. rconstructors*.

  (*red_expr_bitwise_op*)
  wf_inverts3a. auto with wf_base.

  (*red_expr_bitwise_op_1*)
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. auto. rconstructors*.

  (*red_expr_bitwise_op_2*)
  wf_inverts3a. wf_out_change_state. rconstructors*.

  (*red_expr_binary_op_lazy*)
  wf_inverts3a. inverts H2. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. rconstructors*.
 
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a.  wf_out_change_state. rconstructors*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. auto. rconstructors*.

  wf_inverts3a. wf_out_change_state. rconstructors*.

  (*red_expr_conditional*)
  wf_inverts3a. inverts H1. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. auto. rconstructors*.
 
  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_spec. auto. rconstructors*. cases_if; subst; eapply wf_expr_state_extends; eauto.

  wf_inverts3a. rconstructors*.

  (*red_expr_assign*)
  wf_inverts3a. inverts H0. auto.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_spec. auto. rconstructors*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. wf_inverts. rconstructors*. apply* pr_red_spec. auto. rconstructors*.

  wf_inverts3a. wf_out_change_state. wf_inverts. auto with wf_base.

  wf_inverts3a. wf_inverts. wf_out_change_state. apply* pr_red_expr. rconstructors*.

  wf_inverts3a. wf_inverts. wf_out_change_state. auto with wf_base.

  wf_inverts3a. inverts H1. wf_out_change_state. auto with wf_base.

  wf_inverts3a. wf_out_change_state.

  wf_inverts3a. auto with wf_base.

  (*red_expr_binary_op_coma*)
  wf_inverts3a. auto with wf_base.

  (*red_spec_returns*)
  wf_inverts3a.

  (*red_spec_to_boolean*)
  wf_inverts3a. auto with wf_base.

  (*red_spec_to_number*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  (*red_spec_to_integer*)
  wf_inverts3a.

  wf_inverts3a. auto with wf_base.

  (*red_spec_to_string*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  (*red_spec_object_get*)
  wf_inverts3a. apply* pr_red_expr. inverts Hred. inverts H0. rconstructors*.
  
  (*red_spec_object_put*)
  wf_inverts3a. apply* pr_red_expr. destruct B; subst. rconstructors*.

  (*red_spec_object_can_put*)
  wf_inverts3a. inverts H. destruct B. apply* pr_red_expr.

  (*red_spec_object_has_prop*)
  wf_inverts3a. destruct B; subst. auto with wf_base.

  (*red_spec_object_delete*)
  wf_inverts3a.

  (*red_spec_object_default_value*)
  wf_impossible.

  (*red_spec_object_define_own_prop*)
  wf_inverts3a. inverts H. inverts keep HS. inverts H0. apply* pr_red_expr.
  forwards M:wf_state_wf_objects x0 str. exists* l. inverts M.
  rewrite wf_object_define_own_prop; constructor*.

  (*red_spec_object_has_instance*)
  wf_inverts3a.

  (*red_spec_call*)
  wf_impossible.

  (*red_spec_object_get (again)*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. rconstructors*.

  wf_inverts3a. rconstructors*. inverts H1. inverts H3. simpl in H. subst*.

  wf_inverts3a. wf_inverts. inverts H2.

  wf_inverts3a.

  wf_impossible.

  (*red_spec_object_can_put (again)*)
  wf_inverts3a. forwards* M:pr_red_spec H. constructor*.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. rconstructors*. inverts H. inverts keep H3. forwards M:wf_state_wf_objects x0 str.  exists* l. inverts M. inverts H0. auto.

  auto with wf_base.

  wf_inverts3a. apply* pr_red_expr. constructor*. apply* pr_red_spec. auto. constructor*.

  wf_inverts3a. auto with wf_base.
  
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. destruct Ad. constructor*. inverts H1. inverts H3. assumption.

  rconstructors*.

  rconstructors*.

  (*red_spec_object_put (again)*)
  wf_inverts3a.

  wf_inverts3a. wf_out_change_state. auto with wf_base.

  wf_inverts3a. wf_out_change_state. auto with wf_base. 

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_expr. rconstructors*. subst. rconstructors*.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. rconstructors*. apply* pr_red_spec. auto. constructor*.

  wf_inverts3a. inversion H3. inversion H5.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_expr. constructor*. auto with wf_base. subst. rconstructors*. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  (*red_spec_object_has_prop (again)*)
  wf_inverts3a. auto with wf_base.
  
  wf_inverts3a. rconstructors*.

  (*red_spec_object_delete (again)*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. rconstructors*.

  wf_inverts3a. forwards M:object_rem_property_state_extends H0. forwards* MM:wf_object_rem_property H0. wf_out_change_state. rconstructors*.

  wf_inverts3a. auto with wf_base.

  (*red_spec_object_define_own_prop (again)*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a. cases_if; forwards* HS':wf_set_property str; subst; try constructor*;
  try solve [unfolds unsome_default; destruct Desc ; subst; simpl; inverts H8; simpl; inverts H2; [constructor*|auto]| rconstructors*];
  clear HS HC H4 H0 l C x throw; exfalso; apply H1; clear H1; inverts H8; unfolds descriptor_is_generic; unfolds descriptor_is_accessor; unfolds descriptor_is_data; simpl; destruct ov1; destruct ob1; try solve [right; introv H1; inverts H1; inverts H0|right; introv H1; inverts H1; inverts H2|left; auto].
  
  wf_inverts3a. rconstructors*.

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a.
  
  wf_inverts3a. exfalso. clear Hred HS HC H4 pr_red_expr C l x throw o. inverts H8. inverts H7.
  unfolds descriptor_is_generic; unfolds descriptor_is_data; unfolds descriptor_is_accessor; simpl; simpl in H. simpl in H0. apply* H0. symmetry. apply* prop_eq_True_back.
  (*the new rule for spec_object_define_own_prop_5_a is used here*)

  wf_impossible.

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a.

  wf_inverts3a. forwards* HS':wf_set_property str A'. destruct A; subst; simpl; rconstructors*; inverts H7; simpl; inverts H8; inverts H; simpl; auto.
  inverts HS'. auto with wf_base. 

  (*red_spec_prim_value_get*)
  wf_inverts3a.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. wf_inverts. inverts H0. constructor*.
  
  (*red_spec_ref_put_value_value*)
  wf_inverts3a. apply* pr_red_expr. constructor*. inverts HS. inverts wf_state_prealloc_global. inverts H1. constructor*. unfolds. rewrite Heap.indom_equiv_binds. exists x; auto.

  wf_inverts3a. apply* pr_red_expr. cases_if; subst; simpl; rconstructors*; destruct r; simpl in H0; inverts H3; subst; inverts H4; auto.

  wf_inverts3a. apply* pr_red_expr. rconstructors*. destruct r; subst. simpl in H. subst. wf_inverts. wf_inverts. inverts H1. assumption.
 
  wf_inverts3a.

  wf_inverts3a. wf_inverts. inverts H0. auto with wf_base.

  (*red_spec_env_record_has_binding*)
  wf_inverts3a. apply* pr_red_expr. rconstructors*. inverts* HS.

  rconstructors*.

  wf_inverts3a.

  (*red_spec_env_record_create_mutable_binding*)
  wf_inverts3a. apply* pr_red_expr. constructor*. inverts* HS.

  wf_inverts3a. subst. forwards* M:wf_env_record_write_decl_env str prim_undef. inverts* M. constructor*. auto with wf_base.

  wf_inverts3a.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. apply* pr_red_expr. constructor*; auto with wf_base. subst. rconstructors*.

  wf_inverts3a. auto with wf_base.

  (*red_spec_env_record_set_mutable_binding*)
  wf_inverts3a. apply* pr_red_expr. constructor*. inverts* HS.

  wf_inverts3a. apply* pr_red_expr. cases_if; subst; simpl; auto with wf_base. forwards* M:wf_env_record_write_decl_env S L x mu v. inverts* M. rconstructors*.

  wf_inverts3a. auto with wf_base.

  (*red_spec_env_record_get_binding_value*)
  wf_inverts3a. apply* pr_red_expr. constructor*. inverts* HS.

  wf_inverts3a. apply* pr_red_expr. cases_if; subst; simpl; auto with wf_base. rconstructors*. unfolds decl_env_record_binds. inverts H2. forwards* M:H3.

  wf_inverts3a.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. rconstructors*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr. constructor*. eapply wf_value_state_extends; eauto.

  (*red_spec_env_record_delete_binding*)
  wf_inverts3a. apply* pr_red_expr. constructor*. inverts* HS.

  wf_inverts3a. cases_if; try solve [inverts H0; rconstructors*]. inverts H0. forwards* E:wf_env_record_write str (decl_env_record_rem Ed x). constructor. inverts H5. apply* wf_decl_env_record_rem.
  rconstructors*.

  rconstructors*.

  wf_inverts3a.

  (*red_spec_record_implicit_this_value*)
  wf_impossible.

  wf_impossible.

  wf_impossible.

  (*red_spec_env_record_create_immutable_binding*)
  wf_inverts3a. forwards* M:wf_env_record_write_decl_env S str L x prim_undef. inverts* M. subst. rconstructors*.

  wf_inverts3a. forwards* M:wf_env_record_write_decl_env str v. inverts M; subst; rconstructors*.

  wf_inverts3a.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  (*red_spec_binding_inst_function_decls*)
  rconstructors*.
  
  wf_impossible.

  (*red_spec_binding_inst_var_decls*)
  rconstructors*.
  
  wf_inverts3a.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  (*red_spec_binding_inst*)
  wf_inverts3a. inverts keep HC. rewrite H in wf_execution_ctx_wf_variable_env. inverts wf_execution_ctx_wf_variable_env. auto with wf_base.

  wf_inverts3a. 

  wf_impossible.

  wf_inverts3a.

  wf_inverts3a. apply* pr_red_expr. constructor*. apply* pr_red_expr. forwards* M:wf_prog_funcdecl_nil H3. subst. rewrite M. constructor*.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a. 

  wf_inverts3a. 

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a. wf_out_change_state. apply* pr_red_expr.

  wf_inverts3a. (*the new rule for spec_binding_inst_8 is used here*)

  (*red_spec_object_has_instance*)
  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. auto with wf_base.

  wf_inverts3a. wf_inverts3a. auto with wf_base.

  wf_inverts3a. apply* pr_red_expr. constructor*.
  inverts H. inverts H0. inverts HS. forwards* M:wf_state_wf_objects x str. inverts* M.

  auto with wf_base.

  auto with wf_base.

  wf_inverts3a. auto with wf_base.

  (*red_spec_call*)
  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  (*red_spec_error*)
  wf_inverts3a. apply* pr_red_expr. constructor*. apply* pr_red_expr. rconstructors*. inverts HS. auto.

  wf_inverts3a. rconstructors*.

  wf_inverts3a. rconstructors*.

  rconstructors*.

  (*red_spec_build_error*)
  wf_inverts3a.
  forwards* M1: object_alloc_state_extends H0.
  forwards* M2: wf_object_alloc str O H0. unfolds object_new. unfolds object_create.  subst; constructor*; auto. simpl. introv HH. assert (HH':exists (AA:attributes), Heap.binds Heap.empty x AA). exists* A. rewrite <- Heap.indom_equiv_binds in HH'.
    unfolds Heap.indom. rewrite Heap.dom_empty in HH'. inverts HH'.
  inverts M2. auto with wf_base.

  wf_inverts3a. rconstructors*.

  wf_inverts3a. 

  wf_inverts3a. wf_out_change_state. wf_inverts. forwards* M:wf_set_property str H; rconstructors*. unfolds; inverts H5; apply* H0. inverts M. unfolds; inverts H1; apply* H6; inverts H5; apply* H1.

  wf_impossible.

  wf_impossible.
  
  wf_impossible.

  wf_impossible.
  
  wf_impossible.

  (*red_spec_call_error*)
  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

  wf_impossible.

Admitted.

(*Qed.*)



Hint Resolve pr_red_spec : core.
Hint Resolve pr_red_expr : core.

Hint Resolve pr_red_spec : wf_base.
Hint Resolve pr_red_expr : wf_base.

(*tactic used in the proof of pr_red_stat*)
Ltac wf_inverts_stat :=
  match goal with
    | [H:wf_ext_stat _ _ _ |-_] => inverts H
    | [H:wf_stat _ _ _ |-_] => inverts H
  end.

Ltac wf_inverts_stat_aux :=
  match goal with
    | [H:wf_switchbody _ _ (switchbody_nodefault _) |-_] => inverts H
    | [H:wf_switchbody _ _ (switchbody_withdefault _ _ _) |-_] => inverts H
    | [H:wf_switchclause _ _ (switchclause_intro _ _) |-_] => inverts H
    | [H:wf_ostat _ _ None |-_] => clear H
    | [H:wf_ostat _ _ (Some _) |-_] => inverts H
    | [H:wf_ostringstat _ _ None |-_] => clear H
    | [H:wf_ostringstat _ _ (Some _) |-_] => inverts H
    | [H:wf_liststat _ _ nil |-_] => clear H
    | [H:wf_liststat _ _ (List.cons _ _) |-_] => inverts H
    | [H:wf_listswitchclause _ _ nil |-_] => clear H
    | [H:wf_listswitchclause _ _ (List.cons _ _) |-_] => inverts H
  end.


(*lemmas used in the proof of pr_red_stat*)
Lemma lexical_env_alloc_state_extends : forall (S S':state) (lex lex':lexical_env) (E:env_record),
  (lex',S') = lexical_env_alloc S lex E ->
  state_extends S' S.
Proof.
  introv HH. unfolds lexical_env_alloc. unfolds env_record_alloc. destruct S. destruct state_fresh_locations. inverts HH.
  unfolds. split. simpl. apply* @heap_extends_refl.
  simpl. apply* @heap_write_extends. apply* eq_env_loc_dec.
Qed.


Lemma wf_lexical_env_alloc : forall (S S':state) (str:strictness_flag) (lex lex':lexical_env) (E:env_record),
  wf_state S ->
  wf_lexical_env S str lex ->
  wf_env_record S str E ->
  (lex',S') = lexical_env_alloc S lex E ->
  wf_state S' /\ wf_lexical_env S' str lex'.
Proof.
  introv HS Hl HE HH.
  forwards* M:lexical_env_alloc_state_extends. split.
  (*wf_state*)
    unfolds lexical_env_alloc. unfolds env_record_alloc. destruct S. destruct state_fresh_locations. inverts HH.
    inverts HS. constructor*.
    (*wf_state_wf_objects*)
      introv EE. unfolds object_binds. clear wf_state_prealloc_global wf_state_prealloc_native_error_proto wf_state_wf_env_records wf_state_env_loc_global_env_record Hl. simpl in EE; simpl in wf_state_wf_objects.
      forwards* MM: wf_object_state_extends str0 obj M.
    (*wf_state_prealloc_global*)
      clear wf_state_wf_objects wf_state_prealloc_native_error_proto wf_state_wf_env_records wf_state_env_loc_global_env_record Hl. inverts wf_state_prealloc_global. exists* x.
    (*wf_state_wf_env_records*)
      clear wf_state_wf_objects wf_state_prealloc_global wf_state_prealloc_native_error_proto wf_state_env_loc_global_env_record Hl.
      introv Hb. inverts Hb. unfolds in H. simpl in H. apply Heap.binds_write_inv in H. inverts H. inverts H0. 
      clear wf_state_wf_env_records. inverts HE.
        constructor; unfolds wf_decl_env_record. introv Hb. forwards* MM:H Hb. inverts* MM.
        constructor; unfolds wf_object_loc. unfolds* object_indom.
      inverts H0. eapply wf_env_record_state_extends; eauto.
    (*wf_state_env_loc_global_env_record*)
      simpl. simpl in wf_state_env_loc_global_env_record. unfolds Heap.indom.
      rewrite Heap.dom_write. apply* in_union_get_1.
  (*wf_lexical_env*)
    unfolds lexical_env_alloc. unfolds env_record_alloc. destruct S. destruct state_fresh_locations. inverts HH.
    constructor*. constructor*. simpl. find_in_heap.
    eapply wf_lexical_env_state_extends; eauto.
Qed.


Lemma wf_execution_ctx_with_lex : forall (S:state) (str:strictness_flag) (C:execution_ctx) (lex:lexical_env),
  wf_execution_ctx S str C ->
  wf_lexical_env S str lex ->
  wf_execution_ctx S str (execution_ctx_with_lex C lex).
Proof.
  introv HC Hlex. destruct C. inverts HC.
  simpl in wf_execution_ctx_wf_lexical_env; simpl in wf_execution_ctx_this_binding. unfolds execution_ctx_with_lex. constructor*.
Qed.


Ltac appredspec :=
  match goal with
    | [H:red_spec _ _ _ ?s |- wf_specret _ _ ?s] => forwards*: pr_red_spec H; auto
  end.


Hint Resolve pr_red_spec : wf_base.
Hint Extern 1 => appredspec : wf_base.
Hint Extern 0 => wf_inverts_stat_aux : wf_base.


Theorem pr_red_stat : forall (S:state) (C:execution_ctx) (et:ext_stat) (o:out) (str:strictness_flag),
  red_stat S C et o ->
  wf_state S ->
  wf_execution_ctx S str C ->
  wf_ext_stat S str et ->
  wf_out S str o.
Proof.
  introv Hred. induction Hred; introv HS HC Het;  try solve [apply* wf_out_of_ext_stat]; try solve [wf_inverts_stat; repeat wf_inverts_stat_aux; solve [auto with wf_base | wf_inverts_stat; auto with wf_base ]].

  (*red_stat_block*)
  wf_inverts_stat. wf_inverts_stat.
  assert (M:wf_stat S str t). clear Hred1 Hred2 IHHred1 IHHred2 HS HC. induction ts; inverts* H1.
  assert (MM:wf_liststat S str ts). clear Hred1 Hred2 IHHred1 IHHred2 HS HC M. induction ts; inverts* H1. constructor*.
  auto with wf_base.

  wf_inverts_stat. wf_inverts3a. wf_out_change_state. constructor*. subst.
    destruct R; destruct res_value; simpl; unfolds res_overwrite_value_if_empty; cases_if; simpl; auto. inverts H7;  constructor*.

  (*red_stat_var_decl_cons*)
  wf_inverts_stat. wf_inverts_stat. inverts H1. apply* IHHred2.
  assert (Ho1:wf_out S str o1). apply* IHHred1.
  inverts keep Ho1. apply wf_stat_var_decl_1 with S'; auto.
    apply Forall_weaken with (wf_var_decl S str); auto. unfolds. intros. eapply wf_var_decl_state_extends; eauto.

  (*red_stat_var_decl_1*)
  wf_inverts_stat. inverts H2. wf_inverts. auto with wf_base.

  (*red_stat_var_decl_item_some*)
  wf_inverts_stat. apply* IHHred. inverts H1. constructor*.
  apply* pr_red_spec. constructor*. inverts* HC.
  
  (*red_stat_var_decl_item_1*)
  wf_inverts_stat. wf_inverts. wf_inverts. wf_out_change_state.
  apply* IHHred. constructor*.
  apply* pr_red_spec. auto. constructor*.

  (*red_stat_var_decl_item_2*)
  wf_inverts_stat. wf_inverts3a. wf_out_change_state.
  apply* IHHred. constructor*. apply* pr_red_expr. rconstructors*.

  (*red_stat_if*)
  wf_inverts_stat. wf_inverts_stat. apply* IHHred. inverts* H6; constructor*; auto with wf_base.

  (*red_stat_do_while*)
  wf_inverts_stat. wf_inverts3a. subst. cases_if; auto with wf_base. wf_out_change_state. apply* IHHred. constructor*. destruct R; inverts* H5.

  (*red_stat_while*)
  wf_inverts_stat. wf_inverts3a. subst. cases_if; auto with wf_base.
  destruct R; inverts* H5. auto with wf_base.
  
  (*red_stat_for*)
  wf_inverts_stat. subst; cases_if; auto with wf_base. wf_inverts3a. wf_out_change_state. apply* IHHred. rconstructors*. inverts* H4.

  (*red_stat_with*)
  wf_inverts_stat. wf_inverts3a.
  unfolds lexical_env_alloc_object.
  forwards* M1: lexical_env_alloc_state_extends S lex.
  forwards* M2: wf_lexical_env_alloc S str lex. subst; inverts* HC. constructor*. inverts* M2.
  wf_out_change_state. wf_out_change_state. apply* IHHred. subst*. destruct C; constructor*; simpl. inverts* HC. apply wf_lexical_env_state_extends with S; auto. inverts* HC. apply wf_value_state_extends with S; auto.
  constructor*. apply wf_stat_state_extends with S; auto.

  (*red_stat_switch*)
  wf_inverts_stat. repeat wf_inverts_stat_aux. wf_inverts3a. wf_out_change_state. auto with wf_base.

  wf_inverts_stat. repeat wf_inverts_stat_aux. wf_inverts3a. wf_out_change_state. auto with wf_base.

  wf_inverts_stat. subst. wf_inverts3a. auto with wf_base.

  wf_inverts_stat. wf_inverts3a. destruct R. cases_if; subst; auto with wf_base.

  wf_inverts_stat. wf_inverts3a. subst. constructor*. apply* wf_res_overwrite_value_if_empty.

  wf_inverts_stat. wf_inverts3a. cases_if; subst; auto with wf_base.

  wf_inverts_stat. wf_inverts3a. constructor*. apply* wf_res_overwrite_value_if_empty.

  wf_inverts_stat. wf_inverts3a. cases_if; subst; auto with wf_base.

  wf_inverts_stat. wf_inverts3a. constructor*. apply* wf_res_overwrite_value_if_empty.

  (*red_stat_label*)
  wf_inverts_stat. subst. wf_inverts3a. auto with wf_base.

  (*red_stat_try*)
  wf_inverts_stat. wf_inverts3a.
  forwards* M1: lexical_env_alloc_state_extends S lex. forwards* M2: wf_lexical_env_alloc S lex. inverts* HC. subst. apply wf_lexical_env_state_extends with S0; auto. apply* wf_execution_ctx_wf_lexical_env. constructor*. unfolds*. introv Hb; unfolds in Hb; exfalso; apply* @heap_empty_binds_false. inverts M2.
  wf_out_change_state. wf_out_change_state. apply* IHHred. apply wf_execution_ctx_state_extends with S; auto. constructor*. apply* pr_red_expr. apply wf_execution_ctx_state_extends with S; auto. constructor*. subst. inverts* H8. inverts* H12; subst. simpl in H3. subst. wf_inverts. wf_state_extends. apply wf_stat_state_extends with S; auto. apply wf_ostat_state_extends with S; auto.

  wf_inverts_stat. wf_inverts3a.
  forwards M:wf_execution_ctx_with_lex S str C lex'. apply* wf_execution_ctx_state_extends. wf_state_extends.
  wf_out_change_state. apply* IHHred2. apply wf_execution_ctx_state_extends with S0; auto. constructor*. apply* IHHred1. constructor*. apply wf_stat_state_extends with S0; auto. apply wf_ostat_state_extends with S0; auto.
  
Qed.



Theorem pr_red_prog : forall (S:state) (C:execution_ctx) (ep:ext_prog) (o:out) (str:strictness_flag),

  red_prog S C ep o ->
  wf_state S ->
  wf_execution_ctx S str C ->
  wf_ext_prog S str ep ->
  wf_out S str o.
Proof.
  introv Hred. inductions Hred; introv HS HC Hep.
  (*case red_prog_abort*)
    eapply wf_out_of_ext_prog; eauto.
  (*case red_javascript_intro_1*)
    inverts Hep. inverts H1. inverts H2.
    wf_out_change_state. apply* IHHred.
  (*case red_prog_nil*)
    apply* wf_out_ter. (*apply state_extends_refl.*)
    apply wf_res_intro; constructor*.
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
Qed.



(*state_initial because that's what red_javascript does*)
Theorem pr_red_javascript : forall (p:prog) (str:strictness_flag) (o:out),
  (forall str':strictness_flag, wf_value state_initial str' object_prealloc_global_proto) ->
  red_javascript p o ->
  wf_prog state_initial str p ->
  wf_out state_initial (prog_intro_strictness p) o.
Proof.
  introv Hwf Hred Hp. inverts Hred.
  eapply pr_red_prog. eauto.
  (*wf_state_initial*)
    apply* wf_state_initial.
  (*wf_execution_ctx_initial*)
    rewrite add_infos_prog_false.
    apply wf_execution_ctx_initial.
  (*wf_ext_prog*)
    assert (Ho1:wf_out state_initial (prog_intro_strictness p) o1).
      eapply pr_red_expr.
      (*red_expr*)
        rewrite add_infos_prog_false in H2.
        apply H2.
      (*wf_state_initial*)
        apply* wf_state_initial.
      (*wf_execution_ctx_initial*)
        apply wf_execution_ctx_initial.
      (*wf_ext_expr*)
        apply wf_spec_binding_inst.
        rewrite <- add_infos_prog_false.
        eapply wf_prog_intro_strictness.
        apply wf_add_infos_prog_strictness_false.
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
        apply wf_add_infos_prog_strictness_false.
        eapply wf_prog_state_extends; eauto.
Qed.
