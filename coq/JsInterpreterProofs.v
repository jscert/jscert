Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSemanticsAux JsWf JsWfAux JsSafety JsScopes JsInterpreter.


(**************************************************************)
(** ** Correctness of proto_comp. *)

Section Proto.

(** Termination of [proto_comp] *)

Inductive proto_closer : binary (heap * field * loc) :=
| proto_closer_next : forall h f (l l':loc),
ok_heap h ->
~ indom h l f ->
binds h l field_proto l' ->
proto_closer (h, f, l') (h, f, l).

Lemma proto_closer_wf : wf proto_closer.
Proof.
intros [[h f] l]. constructor.
intros [[h' f'] l'] H. inverts H as O D B1.
lets~ N: ok_heap_protochain B1. inverts N as B2 P.
false. forwards*: ok_heap_null B1.
forwards E: binds_func_loc B2 B1. subst.
clears O B1 B2 D.
induction P; constructor; intros [[h2 f2] l2] M; inverts M.
false. forwards*: ok_heap_null.
forwards E: binds_func_loc H H8. subst*.
Qed.

Lemma proto_comp_fix : forall h f l,
  ok_heap h ->
  proto_comp h f l = proto_comp_body proto_comp h f l.
Proof.
applys~ (FixFun3_fix_partial proto_closer). apply proto_closer_wf.
intros h1 f1 l1 proto_comp1 proto_comp2 O Cont. unfolds.
repeat case_if~.
sets_eq v: (read h1 l1 field_proto). destruct~ v.
applys~ Cont. constructor~. rewrite* binds_equiv_read.
Qed.

(** Correctness and completeness of [proto_comp] *)

Hint Constructors proto.

Lemma proto_comp_correct : forall h f l l',
ok_heap h ->
bound h l ->
proto_comp h f l = l' ->
proto h f l l'.
Proof.
introv OK B E. forwards~ PC: ok_heap_protochain_bound B.
induction PC.
 lets (f'&B1): B. rewrite indom_equiv_binds in B1.
lets (v&B2): B1. forwards*: ok_heap_null B2.
 rewrite~ proto_comp_fix in E.
unfold proto_comp_body in E.
case_if~. subst~.
case_if~. subst~.
case_if~ in E.
 rewrite~ binds_equiv_read in H.
rewrite H in E. rewrite~ <- binds_equiv_read in H.
apply* proto_next.
tests: (l'0 = loc_null).
rewrite~ proto_comp_fix in E.
 unfolds in E. case_if. subst~.
apply~ IHPC. inverts* PC. apply* binds_bound.
 false n1.
lets (v&B1): B. rewrite indom_equiv_binds in B1.
lets (v'&B2): B1. forwards~ B3: ok_heap_protochain B2.
inverts* B3. rewrite* indom_equiv_binds.
Qed.

Lemma proto_comp_complete : forall h f l l',
ok_heap h ->
bound h l ->
proto h f l l' ->
proto_comp h f l = l'.
Proof.
introv OK B P. induction P;
 rewrite~ proto_comp_fix; unfold proto_comp_body; case_if~.
case_if*.
  subst. lets (f'&B'): B. rewrite~ indom_equiv_binds in B'.
   lets (v&B''): B'. forwards*: ok_heap_null B''.
  case_if~. case_if~.
    rewrite (binds_read H0).
     tests: (l' = loc_null).
       asserts: (l'' = loc_null).
         apply* proto_func.
       subst. rewrite~ proto_comp_fix. unfold proto_comp_body. case_if*.
      apply~ IHP.
       forwards~: ok_heap_ok_value H0.
       inverts~ H1. inverts* H2. apply* indom_bound.
    false n1. rewrite* indom_equiv_binds.
Qed.

End Proto.


(**************************************************************)
(** ** Correctness of scope_comp. *)

Section Scopes.

(** Correctness and completeness of [scope_comp] *)

Lemma scope_comp_correct : forall h f L l',
  scope_comp h f L = l' ->
  ok_heap h ->
  ok_scope h L ->
  scopes h f L l'.
Proof.
  introv E OK OKL.
  lets~ FOK: ok_scope_all_bound (rm OKL) OK.
  gen h f L l'. induction L; introv OKL E.
  inverts E. constructor*.
  simpls. inverts OKL as (Ba & BL).
  lets~ (l&Hl): proto_defined h f a. apply* indom_bound.
  assert (forall l', proto_comp h f a = l' -> l = l').
    introv E'. lets~: proto_comp_correct E'.
      apply* indom_bound.
      apply* proto_func.
  forwards: (rm H); [ reflexivity | ]. subst. case_if~.
    constructor~.
     apply~ proto_comp_correct.
     apply* indom_bound.
    apply* scopes_here.
Qed.

Lemma scope_comp_complete : forall h f L l',
  scopes h f L l' ->
  ok_heap h ->
  ok_scope h L ->
  scope_comp h f L = l'.
Proof.
  introv Sc OK OKL. forwards~ FOK: ok_scope_all_bound (rm OKL).
  induction Sc; simpls~.
  asserts Eq: (proto_comp h f l = l').
    forwards~: proto_comp_complete H. inverts* H.
      apply* indom_bound.
      apply* binds_bound.
   inverts FOK. rewrite Eq. forwards~: proto_comp_correct Eq. case_if*.
  inverts FOK. case_if~. false. lets*: proto_comp_complete H.
  (* LATER: use [case_if* as C] *)
Qed.

End Scopes.


(**************************************************************)
(** ** Correctness of getvalue_comp. *)

Section Getvalue.

(** Correctness and completness of [getvalue_comp] *)

Lemma getvalue_comp_correct_ref : forall h l f v,
  getvalue_comp h (Ref l (field_normal f)) = Some v ->
  ok_heap h ->
  bound h l ->
  getvalue h (Ref l (field_normal f)) v.
Proof.
  introv E OK B. unfolds in E. case_if~.
  asserts [l' Hl']: (exists l', proto_comp h (field_normal f) l = l').
    destruct* proto_comp.
  rewrite Hl' in E. case_if~; inverts~ E.
    apply~ getvalue_ref_null. subst. apply* proto_comp_correct.
    lets~ M: proto_comp_correct Hl'. apply* getvalue_ref_not_null.
      applys~ read_binds. apply* proto_indom.
Qed.

Lemma getvalue_comp_correct : forall h r v,
  getvalue_comp h r = Some v ->
  ok_ret_expr h r ->
  ok_heap h ->
  getvalue h r v.
Proof.
  introv E R OK. unfolds getvalue_comp.
  destruct r as [|[l f]].
    inverts E. constructor.
    asserts [f' Hf]: (exists f', f = field_normal f').
      destruct* f; false.
     subst. apply~ getvalue_comp_correct_ref. case_if~.
      inverts R as R. inverts* R.
      apply* indom_bound.
Qed.

Lemma getvalue_comp_complete : forall h r v,
  getvalue h r v ->
  ok_heap h ->
  getvalue_comp h r = Some v.
Proof.
  introv Gv OK. unfold getvalue_comp. induction Gv.
  fequals.
  case_if~. forwards~ M: proto_comp_complete H.
    inverts H; tryfalse. apply* binds_bound. applys* binds_bound.
   rewrite M. case_if~. fequals. applys* binds_read.
  case_if~. forwards~: proto_comp_complete H. (* ARTHUR: can you factorize the pattern with the other case? *)
    inverts H; tryfalse. apply* binds_bound.
   case_if*.
Qed.

End Getvalue.


(**************************************************************)
(** ** Conversion of returned expressions *)

Inductive ret_res_expr : ret -> res_expr -> Prop :=
  | ret_res_expr_ret_expr : forall r,
    ret_res_expr (ret_ret_expr r) (res_expr_normal r)
  | ret_res_expr_throw : forall v,
    ret_res_expr (ret_throw v) (res_expr_throw v).

Inductive ret_res_prog : ret -> res_prog -> Prop :=
  | ret_res_prog_ret_expr : forall r,
    ret_res_prog (ret_ret_expr r) (res_prog_normal r)
  | ret_ret_expr_throw : forall v,
    ret_res_prog (ret_throw v) (res_prog_throw v).


(**************************************************************)
(** ** Lemmas for the correctness of the interpreter *)

Section Correctness.

Global Instance out_comparable : Comparable out.
Proof.
  (* Warning: This proof is classical, and is only there for the proofs.
      It shouldn't be extracted. *)
  (* TODO: do we want/need a version that can be extracted? *)
      (* Martin: I don't thing so for this case: I'm just using it to apply the lemmas `elim_*'. *)
  applys (@comparable_beq out) (fun (o1 o2 : out) =>
    If o1 = o2 then true else false). (* todo: remove type annot *)
  split; introv E.
   case_if*.
   subst; case_if*.
Qed.

Lemma wrong_not_ret_expr : forall h h' r re,
  ret_res_expr r re ->
  wrong h <> out_return h' r.
Proof.
  introv E. unfold wrong.
  destruct Mnostuck.
   inverts E; discriminate.
   discriminate.
Qed.

Lemma wrong_not_ret_prog : forall h h' r re,
  ret_res_prog r re ->
  wrong h <> out_return h' r.
Proof.
  introv E. unfold wrong.
  destruct Mnostuck.
   inverts E; discriminate.
   discriminate.
Qed.

Lemma stat_ret_res_expr_to_prog : forall (r : ret) (re : res_prog),
  ret_res_prog r re ->
  exists re', ret_res_expr r re' /\ forall h s h',
   red_stat h s (ext_res_expr_res_prog (out_expr_ter h' re'))
     (out_prog_ter h' re).
Proof.
  introv E.
  destruct r; inverts E.
    eexists. splits~. constructor~.
     introv. apply~ red_stat_ext_res_expr_res_prog_normal.
    eexists. splits~. constructor~.
     introv. apply~ red_stat_ext_res_expr_res_prog_throw.
Qed.

Lemma ret_not_wrong_expr : forall h h' r re,
  ret_res_expr r re ->
  out_return h' r <> wrong h.
Proof. introv O E. symmetry in E. forwards*: wrong_not_ret_expr E. Qed.

Lemma ret_not_wrong_prog : forall h h' r re,
  ret_res_prog r re ->
  out_return h' r <> wrong h.
Proof. introv O E. symmetry in E. forwards*: wrong_not_ret_prog E. Qed.

Lemma elim_if_success : forall r0 k h r,
  if_success r0 k = out_return h r ->
  (r0 = out_return h r /\ forall v, r <> ret_ret_expr v) \/
    exists r1 h0, r0 = out_return h0 (ret_ret_expr r1).
Proof.
  introv E. destruct r0.
   destruct* r0.
    inverts E. left. split~. introv. discriminate.
    simpls. inverts~ E. left. split~. introv. discriminate.
   simpls. inverts* E.
   simpls. inverts* E.
Qed.

Lemma elim_if_defined : forall A h f r (a : option A),
  if_defined h a f = r ->
  a = None \/ exists b, a = Some b.
Proof. introv E. destruct* a. Qed.

Lemma elim_if_defined_else : forall A (o : option A) k1 k2 r,
  if_defined_else o k1 k2 = r ->
  o = None \/ exists a, o = Some a.
Proof. introv E. destruct* o. Qed.

Lemma elim_if_success_value : forall r0 k h r,
  if_success_value r0 k = out_return h r ->
  (r0 = out_return h r /\ forall v, r <> ret_ret_expr v) \/
  (exists v h, r0 = out_return h (ret_ret_expr v) /\ getvalue_comp h v = None) \/
  exists v h b, r0 = out_return h (ret_ret_expr v) /\ getvalue_comp h v = Some b.
Proof.
  introv E.
  unfolds in E.
  forwards~ [OK | (v&h'&E')]: elim_if_success E.
  right. subst. simpls.
  forwards~ [? | ?]: elim_if_defined E.
  rewrite H in E. simpls.
   left*.
  lets (b&E'): H. right*.
Qed.

Lemma elim_if_success_or_throw : forall o k1 k2 h r,
  if_success_or_throw o k1 k2 = out_return h r ->
  (o = out_return h r /\ (forall v, r <> ret_ret_expr v) /\ forall v, r <> ret_throw v) \/
  (exists v h, o = out_return h (ret_ret_expr v)) \/
  (exists v h, o = out_return h (ret_throw v)).
Proof.
  introv E. unfolds in E. destruct o; tryfalse.
  destruct~ r0.
   branch* 2.
   branch* 3.
   branch 1. splits~.
    introv. inverts~ E. discriminate.
    introv. inverts~ E. discriminate.
Qed.

Lemma elim_if_is_ref : forall h o k r,
  if_is_ref h o k = r ->
  ((exists h', wrong h' = r) /\ exists v, o = ret_expr_value v)
    \/ exists l f, o = ret_expr_ref (Ref l f).
Proof.
  introv E. destruct* o.
  inverts E. right. destruct* r0.
Qed.

Lemma elim_if_is_null_ref : forall r k1 k2 rf,
  if_is_null_ref r k1 k2 = rf ->
  (exists v, r = ret_expr_value v) \/
  (exists l f, l <> loc_null /\ r = Ref l f) \/
  exists f, r = Ref loc_null f.
Proof.
  introv E. destruct r.
   left*.
   right. destruct r. simpl in E.
    case_if.
     subst*.
     left*.
Qed.

Lemma elim_if_is_field_normal : forall h f k r,
  if_is_field_normal h f k = r ->
  (r = wrong h) \/ exists f', f = field_normal f'.
Proof. introv E. destruct f; simpls*. Qed.

Lemma elim_if_eq : forall l0 h o k1 k2 r,
  if_eq l0 h o k1 k2 = r ->
  o = None \/
  (exists v, o = Some v /\ r = wrong h) \/
  o = Some (value_loc l0) \/
  exists l, o = Some (value_loc l) /\ l <> l0.
Proof.
  introv E. destruct~ o.
  right. destruct v; inverts* E.
  right. tests: (l0 = l).
   left. split~.
   right. exists l. splits~.
Qed.

Lemma elim_if_not_eq : forall l0 h o k r,
  if_not_eq l0 h o k = r ->
  o = None \/
    ((exists h', wrong h' = r) /\ exists v, o = Some v) \/
    exists l, o = Some (value_loc l) /\ l <> l0.
Proof.
  introv E.
  forwards* [eqr | [(v&eqo&eqr) | [eqo | (l&eqo&_)]]]: elim_if_eq E.
   substs. simpls.
    case_if.
    branch 2. splits*.
    tests: (l = l0).
     branch 2. subst. simpls. splits*. case_if*.
     branch 3. exists l. split~.
Qed.

Lemma elim_if_is_string : forall h o k r,
  if_is_string h o k = r ->
  o = None \/
    ((exists h', wrong h' = r) /\ exists v, o = Some v) \/
    exists s, o = Some (value_string s).
Proof. introv E. destruct~ o. right. destruct v; inverts* E. Qed.

Lemma elim_if_binds_field : forall f h l k r,
  if_binds_field f h l k = r ->
  (r = wrong h /\ ~indom h l f) \/
  (exists v, binds h l f v).
Proof.
  introv E.
  unfolds in E. case_if~ in E.
  right. eexists.
  rewrite* binds_equiv_read.
Qed.

Lemma elim_if_binds_field_loc : forall f h l k r,
  if_binds_field_loc f h l k = r ->
  (r = wrong h /\ forall l', ~binds h l f (value_loc l')) \/
  (exists l', binds h l f (value_loc l')).
Proof.
  introv E. unfolds in E.
  lets~ [C1 | C2]: elim_if_binds_field E.
  lets (H&H0): C1. left. split~. introv B.
    false H0. rewrite* indom_equiv_binds.
  unfolds if_binds_field. case_if.
   lets (v&B): (rm C2).
    lets B': B.
    rewrite~ binds_equiv_read in B.
    rewrite B in E.
    destruct v; try (
     left; split~; introv B'';
     forwards~ H: binds_func B'' B'; discriminate H).
    right. auto*.
   false. lets (v&B): (rm C2).
    forwards*: binds_indom.
Qed.

Lemma elim_if_boolean : forall h v k1 k2 r,
  if_boolean h v k1 k2 = r ->
  (r = wrong h /\ forall b, v <> value_bool b) \/
  (v = value_bool true) \/
  (v = value_bool false).
Proof.
  introv E. destruct v; simpls;
    try (left; subst; split; [reflexivity | discriminate]).
  right. destruct b; [left* | right*].
Qed.

Lemma elim_if_binds_scope_body : forall h l k r,
  if_binds_scope_body h l k = r ->
  r = wrong h \/
  (indom h l field_body /\
    indom h l field_scope /\
    exists s f e, read h l field_scope = value_scope s /\
    read h l field_body = value_body f e).
Proof.
  introv E. unfold if_binds_scope_body in E.
  lets* [C1 | C2]: elim_if_binds_field E.
  lets (v&B): (rm C2).
  forwards* I: binds_indom B.
  lets B'': B. unfolds in E.
  rewrite~ binds_equiv_read in B''.
  rewrite B'' in E. case_if~.
  destruct v; try (left~; fail).
  case_if in E.
   lets I': i0. rewrite indom_equiv_binds in I'. lets (b&B'): (rm I').
    rewrite~ binds_equiv_read in B'. rewrite B' in E.
    destruct* b.
   left*.
Qed.

Lemma sub_safety_expr : forall h h' s (e : expr) (r : ret_expr),
    red_expr h s e (out_expr_ter h' r) ->
    ok_heap h -> ok_scope h s ->
    ok_heap h' /\ ok_scope h' s /\ ok_ret_expr h' r.
Proof.
  intros. forwards~ H': safety_expr H.
    compute. trivial.
  inverts H'. splits*.
  applys~ ok_scope_extends H6.
Qed.

Lemma sub_safety_stat : forall h h' s (p : stat) (r : ret_expr),
    red_stat h s p (out_prog_ter h' r) ->
    ok_heap h -> ok_scope h s ->
    ok_heap h' /\ ok_scope h' s /\ ok_ret_expr h' r.
Proof.
  intros. forwards~ H': safety_stat H.
    compute. trivial.
  inverts H'. splits*.
  applys~ ok_scope_extends H6.
Qed.

Lemma sub_safety_prog : forall h h' s (P : prog) (r : ret_expr),
    red_prog h s P (out_prog_ter h' r) ->
    ok_heap h -> ok_scope h s ->
    ok_heap h' /\ ok_scope h' s /\ ok_ret_expr h' r.
Proof.
  intros. forwards~ H': safety_prog H.
    compute. trivial.
  inverts H'. splits*.
  applys~ ok_scope_extends H6.
Qed.

Lemma arguments_comp_correct : forall xs vs lfv,
  arguments_comp xs vs = lfv ->
  arguments xs vs lfv.
Proof.
  induction xs; introv E.
   simpls. subst. constructors.
   destruct vs.
     simpls. rewrite <- E. apply* arguments_nil_values.
     simpls. rewrite <- E. apply* arguments_cons.
Qed.

Lemma arguments_comp_combine : forall lx lv',
  LibList.length lv' = LibList.length lx ->
  Forall3 (fun (x : string) (v0 : value) => = (field_normal x, v0)) lx lv'
    (arguments_comp lx lv').
Proof.
  introv L. forwards~ AC: arguments_comp_correct lx lv'.
  induction AC.
   destruct lv.
    apply* Forall3_nil.
    false.
   false.
   apply* Forall3_cons.
Qed.

(**************************************************************)
(** ** Tactics for the correctness of the interpreter *)

Ltac name_heap_write h' :=
  match goal with |- context [ write ?h ?l ?f ?v ] =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_sub_write h' :=
  match goal with |- context [ write (write ?h ?l ?f ?v) _ _ _ ] =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_write_fields h' :=
  match goal with |- context [ write_fields ?h ?l ?li ] =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_reserve_local_vars h' :=
  match goal with |- context [ reserve_local_vars ?h ?l ?li ] =>
    sets_eq h': (reserve_local_vars h l li) end.
Ltac name_heap_alloc_obj H h' :=
  match goal with |- context [ alloc_obj ?h ?l ?l' ] =>
    sets_eq h': (alloc_obj h l l') end.
Ltac name_heap_write_in H h' :=
  match goal with H: context [ write ?h ?l ?f ?v ] |- _ =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_sub_write_in H h' :=
  match goal with H: context [ write (write ?h ?l ?f ?v) _ _ _ ] |- _ =>
    sets_eq h': (write h l f v) end.
Ltac name_heap_write_fields_in H h' :=
  match goal with H: context [ write_fields ?h ?l ?li ] |- _ =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_sub_write_fields_in H h' :=
  match goal with H: context [ write_fields (write_fields ?h ?l ?li) _ _ ] |- _ =>
    sets_eq h': (write_fields h l li) end.
Ltac name_heap_reserve_local_vars_in H h' :=
  match goal with H: context [ reserve_local_vars ?h ?l ?li ] |- _ =>
    sets_eq h': (reserve_local_vars h l li) end.
Ltac name_heap_alloc_obj_in H h' :=
  match goal with H: context [ alloc_obj ?h ?l ?l' ] |- _ =>
    sets_eq h': (alloc_obj h l l') end.
Ltac name_fresh_for l :=
  match goal with |- context [ fresh_for ?h ] =>
    sets_eq l: (fresh_for h) end.
Ltac name_fresh_for_in H l :=
  match goal with H: context [ fresh_for ?h ] |- _ =>
    sets_eq l: (fresh_for h) end.
Ltac name_out_expr_ter H o :=
  match goal with H: context [ out_expr_ter ?h ?v ] |- _ =>
    sets_eq o: (out_expr_ter h v) end.
Ltac name_out_prog_ter H o :=
  match goal with H: context [ out_prog_ter ?h ?v ] |- _ =>
    sets_eq o: (out_prog_ter h v) end.


(**************************************************************)
(** ** Correctness of the implementation of operators *)

Lemma typeof_comp_correct : forall h v str,
  typeof_comp h v = Some str ->
  ok_heap h ->
  typeof_red h v str.
Proof.
  introv E OK.
  destruct v; try (inverts E; constructor).
  simpl in E. case_if; inverts E.
   rewrite indom_equiv_binds in i. lets (v&B): i.
    apply~ typeof_red_function. exists* v.
   lets OKf: ok_heap_function OK. unfolds in OKf.
   apply~ typeof_red_object. introv (v&B). false n.
    forwards (?&?&?&?&F&?&?): OKf B.
    rewrite* indom_equiv_binds.
Qed.

Inductive proto_closer_for_binary_op_comp : binary (binary_op * heap * value * value) :=
  | proto_closer_for_binary_op_comp_instanceof : forall h (l1 l2 l3 l4:loc),
      ok_heap h ->
      binds h l1 field_normal_prototype (value_loc l3) ->
      binds h l2 field_proto (value_loc l4) ->
      l3 <> l4 ->
      proto_closer_for_binary_op_comp (binary_op_instanceof, h, value_loc l1, value_loc l4) (binary_op_instanceof, h, value_loc l1, value_loc l2).

Lemma proto_closer_for_binary_op_comp_wf : wf proto_closer_for_binary_op_comp.
Proof.
  intros [[[b h] v1] v2]. constructor.
  intros [[[b' h'] v1'] v2'] H. inverts H as O B1 B2 D.
  lets~ N: ok_heap_protochain B2. inverts N as B3 P.
    false. forwards*: ok_heap_null B2.
  forwards~: binds_func_loc B3 B2. subst.
  clears O B1 B2 B3 D.
  induction P; constructor; intros [[[b'' h''] v1''] v2''] M; inverts M.
    false. forwards*: ok_heap_null.
    forwards E: binds_func_loc H H9. subst*.
Qed.

Lemma binary_op_comp_fix : forall h op v1 v2,
  ok_heap h -> binary_op_comp op h v1 v2 = binary_op_comp_body binary_op_comp op h v1 v2.
Proof.
  introv O. applys~ (FixFun4_fix_partial proto_closer_for_binary_op_comp (fun _ h _ _ => ok_heap h)).
    apply proto_closer_for_binary_op_comp_wf.
  introv O1 Cont. unfolds. destruct~ x1.
    repeat case_if~. destruct~ x3. simpl. destruct~ x4.
    case_if~; symmetry; case_if~.
    sets_eq v: (read x2 l field_normal_prototype). destruct~ v.
    sets_eq v: (read x2 l0 field_proto). destruct~ v.
    simpls. repeat case_if~.
    rewrite~ Cont.
    apply~ proto_closer_for_binary_op_comp_instanceof.
      rewrite* binds_equiv_read.
      rewrite* binds_equiv_read.
      auto*.
Qed.

Lemma lazy_binary_op_comp_correct : forall h op v,
  red_expr_lazy_binary_op h op v (option_map (fun v : value => out_expr_ter h v) (lazy_binary_op_comp h op v)).
Proof.
  introv.
  destruct op; try (apply~ red_expr_lazy_binary_op_none; intros; false).
   destruct v; try (apply~ red_expr_lazy_binary_op_none; intros; discriminate).
    destruct b.
     apply~ red_expr_lazy_binary_op_none.
       intros. discriminate.
       intros. false.
     apply* red_expr_lazy_binary_op_and.
   destruct v; try (apply~ red_expr_lazy_binary_op_none; intros; discriminate).
    destruct b.
     apply* red_expr_lazy_binary_op_or.
     apply~ red_expr_lazy_binary_op_none.
       intros. false.
       intros. discriminate.
Qed.

Lemma binary_op_comp_correct : forall b h v1 v2 r,
  binary_op_comp b h v1 v2 = Some r ->
  ok_heap h -> ok_value h v1 -> ok_value h v2 ->
  binary_op_red b h v1 v2 r.
Proof.
  introv E OK O1 O2. rewrite~ binary_op_comp_fix in E.
  destruct b; simpls.
  (* add *)
  destruct v1; destruct v2; simpls; tryfalse.
    inverts E. constructor*.
    inverts E. constructor*.
  (* mult *)
  destruct v1; destruct v2; simpls; tryfalse.
   inverts E. constructor*.
  (* div *)
  destruct v1; destruct v2; simpls; tryfalse.
   inverts E. constructor*.
  (* equal *)
  case_if in E as B; tryfalse. lets (B1&B2): a. inverts~ E.
  rewrite~ value_compare_correct. constructor~.

  (* instanceof *)
  destruct v1; simpls; tryfalse.
  apply~ binary_op_red_instanceof.
  case_if in E.
   inverts E. apply* instanceof_red_value.
   inverts* O2.
    unfolds in H. rewrite~ indom_equiv_binds in H.
    lets (v0 & B): (rm H).
    lets~ N: ok_heap_protochain B.
    clear n v0 B. induction N.
     false. case_if in E.
      set_eq v: (read h l field_normal_prototype) in E.
      destruct v; tryfalse. simpl in E. case_if in E.
      rewrite~ indom_equiv_binds in i0. lets (v & B): i0.
      forwards*: ok_heap_null B.
     gen E; intro E. case_if in E. (* FIXME: It seems there is a bug in `case_if' that make it ignore what stands after a `in' argument. *)
      set_eq v: (read h l field_normal_prototype) in E.
      destruct v; simpls; tryfalse. case_if in E.
      set_eq v: (read h l0 field_proto) in E.
      destruct v; simpls; tryfalse.
      asserts: (l2 = l').
        applys~ binds_func_loc H.
        rewrite* binds_equiv_read.
      subst l'. case_if in E.
       inverts E. subst. apply* instanceof_red_true.
         rewrite* binds_equiv_read.
       apply* instanceof_red_trans.
         rewrite* binds_equiv_read.
        tests: (l2 = loc_null).
          clear IHN. rewrite~ binary_op_comp_fix in E.
           simpl in E. case_if in E.
            inverts E. constructor~.
            false n0. constructor.
          apply~ IHN; clear IHN.
           rewrite~ binary_op_comp_fix in E.
           simpl in E. case_if in E.
            false. inverts~ b.
            apply* E.

  (* in *)
  destruct v1; destruct v2; simpls; tryfalse. inverts E.
  inverts O2.
   inverts H.
    apply~ binary_op_red_in.
      constructor.
    case_if.
     rewrite~ proto_comp_fix. unfold proto_comp_body.
     case_if. rewrite decide_spec. fold_bool. apply* eqb_eq.
   apply~ binary_op_red_in.
     apply~ proto_comp_correct.
      apply* indom_bound.
     rewrite decide_spec. case_if~.
      rewrite* eqb_eq.
      rewrite* eqb_neq.

  (* and *)
  destruct v1; tryfalse. cases_if; tryfalse.
  inverts E.
  constructors~.

  (* or *)
  destruct v1; tryfalse. cases_if; tryfalse.
  inverts E.
  constructors~.

Qed.

Lemma unary_op_comp_correct : forall b h v r,
  unary_op_comp b h v = Some r ->
  unary_op_red b h v r.
Proof.
  introv E.
  destruct b; simpls; tryfalse.

  (* not *)
  destruct v; tryfalse.
  inverts~ E. apply* unary_op_red_not.

  (* void *)
  inverts~ E. apply* unary_op_red_void.
Qed.


(**************************************************************)
(** ** Correctness of the interpreter *)

Lemma run_list_expr_add_value : forall m s h0 es vs vs0 k k' r,
  run_list_expr m h0 s (vs ++ vs0) es k = r ->
  (forall h vs', k' h vs' = k h (LibList.rev vs0 ++ vs')) ->
  run_list_expr m h0 s vs es k' = r.
Proof.
  induction m.
    simpl. intros; subst~.
    introv E T. destruct es; simpls.
     rewrite <- E. rewrite rev_app. apply* T.
    destruct~ run_expr. destruct~ r0. simpls.
     destruct~ getvalue_comp. simpls. apply* IHm.
Qed.

Definition run_expr_correct_def m := forall h s e h' r re,
  run_expr m h s e = out_return h' r ->
  ret_res_expr r re ->
  ok_heap h ->
  ok_scope h s ->
  red_expr h s e (out_expr_ter h' re).

Definition run_stat_correct_def m := forall h s p h' r re,
  run_stat m h s p = out_return h' r ->
  ret_res_prog r re ->
  ok_heap h ->
  ok_scope h s ->
  red_stat h s p (out_prog_ter h' re).

Definition run_prog_correct_def m := forall h s P h' r re,
  run_prog m h s P = out_return h' r ->
  ret_res_prog r re ->
  ok_heap h ->
  ok_scope h s ->
  red_prog h s P (out_prog_ter h' re).

Lemma run_correct_aux : forall m, (run_expr_correct_def m) /\
  (run_stat_correct_def m) /\ (run_prog_correct_def m) /\
  (forall h s h' lv le k e' r re,
  run_list_expr m h s (rev lv) le k = out_return h' r ->
  ret_res_expr r re ->
    (forall lv' h0 h0' (r' : ret) re,
      k h0 lv' = out_return h0' r' ->
      ret_res_expr r' re ->
      LibList.length lv' = (LibList.length lv + LibList.length le)%nat ->
      Forall (ok_value h0) lv' ->
      ok_heap h0 ->
      ok_scope h0 s ->
      extends_proto h h0 ->
      red_expr h0 s (e' lv') (out_expr_ter h0' re)) ->
  Forall (ok_value h) lv ->
  ok_heap h ->
  ok_scope h s ->
  red_expr h s (ext_list_then_1 e' lv le) (out_expr_ter h' re)).
Proof.
  induction m.
    splits*; introv R; false R.
  lets (run_expr_correct&run_stat_correct&run_prog_correct&run_list_expr_correct_aux): IHm.
  clear IHm.
  (* run_list_expr_correct *)
  asserts run_list_expr_correct : (forall h s h' le k e' r re,
  run_list_expr m h s nil le k = out_return h' r ->
  ret_res_expr r re ->
  (forall lv h0 h0' (r' : ret) re,
    k h0 lv = out_return h0' r' ->
    ret_res_expr r' re ->
    LibList.length lv = LibList.length le ->
    Forall (ok_value h0) lv ->
    ok_heap h0 ->
    ok_scope h0 s ->
    extends_proto h h0 ->
    red_expr h0 s (e' lv) (out_expr_ter h0' re)) ->
  ok_heap h ->
  ok_scope h s ->
  red_expr h s (ext_list_then e' le) (out_expr_ter h' re)).
   introv Eq OR F Oh Os.
   apply~ red_expr_ext_list_then.
   apply* run_list_expr_correct_aux.
   apply* Forall_nil.

  splits.
  (* run_expr *)
  introv R OR OK OKL. destruct e; simpl in R;
    try (inverts* R; fail).

  (* this *)
  forwards [(?&_) | (l'&B)]: elim_if_binds_field_loc R.
    forwards*: ret_not_wrong_expr H.
  do 2 unfolds in R. rewrite (binds_read B) in R.
  forwards I: binds_indom B.
  case_if~ in R. inverts R. inverts OR.
  apply* red_expr_expr_this.
    apply* scope_comp_correct.
  apply~ proto_comp_correct.
  sets_eq ls: (scope_comp h' field_this s).
  symmetry in EQls. forwards* Pro: scope_comp_correct EQls.
  inverts Pro.
    rewrite <- H in B.
    rewrite* proto_comp_fix in B.
    unfold proto_comp_body in B. case_if~ in B.
    forwards*: ok_heap_null B.
  inverts keep H; tryfalse.
    exists~ field_this.
    apply* binds_bound.
  asserts (lp&Dlp&Plp): (exists l', l' <> loc_null /\ proto h' field_this ls l').
    apply* scopes_proto_not_null.
    intro_subst.
    rewrite* proto_comp_fix in B.
    unfold proto_comp_body in B. case_if~ in B.
    forwards*: ok_heap_null B.
  inverts* Plp.
    exists~ field_this.
  apply* binds_bound.

  (* variable *)
  inverts~ R. inverts OR.
  apply red_expr_expr_variable.
  apply* scope_comp_correct.

  (* literal *)
  inverts R. inverts OR. apply* red_expr_expr_literal.

  (* obj *)
  name_heap_alloc_obj_in R h3.
  sets_eq sl: (split l). destruct sl as [lx lx0].
  asserts OK3: (ok_heap h3).
    subst h3. apply* ok_heap_alloc_obj.
      apply* ok_heap_protochain_indom. applys* ok_heap_special_obj_proto OK.
      right. applys* ok_heap_special_obj_proto OK.
      apply fresh_for_spec.
  asserts OKL3: (ok_scope h3 s).
    applys* ok_scope_extends h.
    subst h3. apply* extends_proto_write.
  name_fresh_for_in EQh3 l0.
  forwards~ R': run_list_expr_correct (ext_expr_object_1 l0 lx) R OR.
    introv R0 OR' SE FO O0 Os0 E0. inverts R0. inverts OR'.
    apply~ red_expr_ext_expr_object_1. apply* arguments_comp_combine.
    transitivity (LibList.length lx0). trivial.
    symmetry. applys~ split_same_length EQsl.
  apply* red_expr_expr_object.
    apply* fresh_for_spec.
    subst h3 l0. trivial.

  (* functions *)
  destruct o.
    (* --named *)
    inverts R. inverts OR.
    apply* red_expr_expr_function_named; apply* fresh_for_spec.
    (* --unnamed *)
    inverts R. inverts OR.
    apply* red_expr_expr_function_unnamed; apply* fresh_for_spec.

  (* access *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
    applys~ red_expr_expr_access R1.
    apply~ red_expr_abort.
    inverts~ OR; tryfalse.
    constructors~.
  rewrite eq1 in R. simpl in R.
  forwards  [eqr | [(eqr&v'&eqo) | (l&eqo&diffno)]]: elim_if_not_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret_expr R.
    lets (h'0&eqr'): eqr. forwards*: wrong_not_ret_expr eqr'.
  rewrite eqo in R. simpl in R.
  case_if* in R; tryfalse.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  applys~ red_expr_expr_access R1.
  forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
    forwards* R2: run_expr_correct eq2.
    applys~ red_expr_ext_expr_access_1 R2.
      apply* getvalue_comp_correct.
    apply~ red_expr_abort.
    inverts OR; tryfalse.
    constructors~.
  rewrite eq2 in R. simpl in R.
  forwards [eqr2 | [(eqr2&v''&eqr2') | (str&eqstr)]]: elim_if_is_string R.
    rewrite eqr2 in R. simpl in R. forwards*: wrong_not_ret_expr R.
    lets (h'0&eqr2''): eqr2. forwards*: wrong_not_ret_expr eqr2''.
  rewrite eqstr in R; simpl in R.
  inverts* R.
  forwards* R2: run_expr_correct eq2.
    constructors*.
  applys~ red_expr_ext_expr_access_1 R2.
    apply* getvalue_comp_correct.
  forwards* O': safety_expr R2.
      compute. trivial.
    inverts~ O'.
  simpl in OR. inverts OR.
  apply~ red_expr_ext_expr_access_2.
    apply* getvalue_comp_correct.

  (* member *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
    applys~ red_expr_expr_member R1.
  rewrite eq1 in R; simpl in R.
  forwards [((?&?)&(?&?)) | (l&f&eq2)]: elim_if_is_ref R.
    rewrite H0 in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eq2 in R. simpl in R.
  forwards [? | (f'&eq3)]: elim_if_is_field_normal R.
    false* wrong_not_ret_expr.
  rewrite eq3 in R. simpl in R.
  subst. inverts~ R.
  forwards~ R1: run_expr_correct eq1 OR.
  assert (f' = s0); subst.
    simpl in OR. inverts OR.
    inverts R1. simpls. inverts H.
    inverts H5. inverts H0.
    inverts H6. simpl in H. inverts H.
    inverts H8. inverts H0.
    inverts~ H5.
  apply* red_expr_expr_member.

  (* new *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
    applys~ red_expr_expr_new R1.
    apply~ red_expr_abort.
    inverts OR; tryfalse.
    constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [eqr | [((h2&eqr)&(v'&eqo)) | (l1&eqo&diffno)]]: elim_if_not_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret_expr R.
    forwards*: wrong_not_ret_expr eqr.
  rewrite eqo in R; simpl in R.
  case_if~ in R.
  forwards~ [? | (Ib&Is&sc&f&e2&Escope&Ebody)]: elim_if_binds_scope_body R.
    subst. forwards*: ret_not_wrong_expr H.
  unfolds in R. do 2 unfold if_binds_field in R at 1. case_if in R. rewrite Escope in R.
  case_if in R. rewrite Ebody in R.
  forwards [(?&?) | (v'&Bv')]: elim_if_binds_field R.
    forwards*: ret_not_wrong_expr H.
  unfolds in R. forwards Iv': binds_indom Bv'. case_if in R.
  rewrite (binds_read Bv') in R.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* S1: safety_expr R1.
    compute. trivial.
  inverts S1 as OK1 OKr1 Ext1.
  applys~ red_expr_expr_new R1.
  forwards~ GV1: getvalue_comp_correct eqo.
  forwards~ R1S: read_binds Escope.
  forwards~ R1B: read_binds Ebody.
  applys~ red_expr_ext_expr_new_1 GV1 R1S R1B Bv'.
  forwards~ S1: ok_scope_extends OKL Ext1.
  apply* run_list_expr_correct. simpl. clear R. (* Martin: There might be other values to clear there. *)
  introv R OR' El FO O0 S0 E1.
  name_heap_reserve_local_vars_in eq3 h7.
  name_heap_write_fields_in EQh7 h6.
  name_heap_write_in EQh6 h5.
  name_heap_sub_write_in EQh5 h4.
  name_heap_alloc_obj_in EQh4 h3.
  (* The following lines are nearly a copy/paste of the corresponding proof in JsSafety. *)
  asserts O3: (ok_heap h3). subst h3. apply~ ok_heap_alloc_obj.
    applys* obj_or_glob_of_value_protochain h1 l1 field_normal_prototype v'.
    right. forwards~: ok_heap_special_obj_proto h1. apply* OK1.
     forwards [(l3&El3)|?]: (value_loc_or_not v').
       subst v'. simpl. forwards OV: ok_heap_ok_value OK1.
        unfolds in OV. forwards~: OV Bv'. case_if*.
       rewrite~ obj_or_glob_of_value_not_loc.
       apply* fresh_for_spec.
  asserts S3: (ok_scope h3 s). subst h3. apply* ok_scope_write.
  asserts O4: (ok_heap h4). subst h4. apply* ok_heap_alloc_obj.
    constructor. apply* fresh_for_spec.
  asserts S4: (ok_scope h4 s). subst h4. apply* ok_scope_write.
  asserts O5: (ok_heap h5). subst h5. forwards~: ok_heap_write_this h4 (fresh_for h3) (fresh_for h0).
    subst h4. apply* binds_write_neq. apply* binds_write_eq.
    apply* fresh_for_spec.
    applys neq_sym. applys~ fresh_binds_neq h3. apply* fresh_for_spec.
     applys~ ok_heap_special_global_this. apply* O3.
    subst h4 h3. do 2 apply* indom_write. apply* indom_write_eq.
  asserts S5: (ok_scope h5 s). subst h5. apply* ok_scope_write.
  asserts O6: (ok_heap h6). subst h6. apply~ ok_heap_write_fields_user.
    subst h5 h4 h3. apply* indom_write. indom_simpl.
    apply* fresh_for_spec.
    apply* arguments_ok_value.
     apply* arguments_comp_correct.
     applys~ Forall_trans value (ok_value h0).
     introv Oa. applys~ ok_value_extends h0.
     subst h5 h4 h3. repeat apply* extends_proto_write_trans.
  asserts S6: (ok_scope h6 s). subst h6. apply* ok_scope_write_fields.
  asserts O7: (ok_heap h7). subst h7. apply~ ok_heap_write_fields_user_undef.
    subst h6 h5 h4. apply* indom_write_fields. apply* indom_write. apply* indom_write_eq.
    apply* fresh_for_spec.
  asserts S7: (ok_scope h7 s). applys* ok_scope_extends.
    subst h7. apply* extends_proto_write_fields_trans.
  assert (ok_scope h7 (fresh_for h3 :: sc)).
    subst h7. apply~ ok_scope_write_fields.
    subst h6. apply~ ok_scope_write_fields.
    subst h5. apply~ ok_scope_write.
    subst h4. apply~ ok_scope_cons.
    subst h3. repeat apply~ ok_scope_write.
    forwards~ Of: ok_heap_function OK1.
    unfolds in Of.
    rewrite* <- binds_equiv_read in Escope.
    forwards: Of l1.
      left. apply Escope.
    applys* ok_scope_extends h1.
    apply* ok_heap_binds_ok_scope.
    apply* indom_write_eq.
  forwards [(eq3&nV) | [(?&h2&eq3&eqv1) | (?&h2&v1&eq3&eqv1)]]: elim_if_success_value R; tryfalse.
    inverts OR'; tryfalse.
     forwards~ R3: run_prog_correct eq3.
       constructor*.
     forwards~ O': safety_prog R3.
       compute. trivial.
     inverts O'.
     apply~ red_expr_ext_expr_new_2.
       apply* fresh_for_spec.
       apply* fresh_for_spec.
       apply* arguments_comp_correct.
       apply~ red_expr_ext_expr_prog.
         substs. apply* R3.
         apply~ red_expr_ext_res_prog_res_expr_throw.
       apply~ red_expr_abort.
         constructor~.
    rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq3 in R. simpls. rewrite eqv1 in R. simpls.
  inverts R.
  forwards~ R3: run_prog_correct eq3.
    constructor*.
  apply~ red_expr_ext_expr_new_2.
   apply* fresh_for_spec.
   apply* fresh_for_spec.
   apply* arguments_comp_correct.
   apply* red_expr_ext_expr_prog.
    substs. apply* R3.
    apply~ red_expr_ext_res_prog_res_expr_normal.
   forwards~ OO3: safety_prog R3.
    compute. trivial.
   inverts~ OO3. inverts OR'.
   apply~ red_expr_ext_expr_new_3.
    apply* getvalue_comp_correct.

  (* call *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
    applys~ red_expr_expr_call R1.
    apply~ red_expr_abort.
    inverts OR; tryfalse.
    constructors~.
  rewrite eq1 in R. simpl in R.
  forwards* [eqr | [(v1&eqo&eqr) | [eqo | (l1&eqo&notEval)]]]: elim_if_eq R.
    rewrite eqr in R. simpl in R. forwards*: wrong_not_ret_expr R.
    forwards*: ret_not_wrong_expr eqr.
    (* --call to eval *) (* Not yet impplemented! *)
    rewrite eqo in R. simpl in R. case_if. inverts R. inverts OR.
    (* -- call to function *)
    rewrite eqo in R. simpl in R. case_if.
    forwards* [? | (Ib&Is&sc&f&e2&Escope&Ebody)]: elim_if_binds_scope_body R.
      subst. forwards*: ret_not_wrong_expr H.
    do 2 unfolds in R. case_if in R. rewrite Escope in R. case_if in R. rewrite Ebody in R.
    forwards* R1: run_expr_correct eq1.
      constructors*.
    forwards* O1: safety_expr R1.
      compute. trivial.
    inverts O1.
    forwards~ G1: getvalue_comp_correct eqo.
    applys~ red_expr_expr_call R1.
    applys~ red_expr_ext_expr_call_1 G1.
    apply~ red_expr_ext_expr_call_2.
      apply* read_binds.
      apply* read_binds.
    forwards* OS1: ok_scope_extends h h1 s.
    apply* run_list_expr_correct. simpl. clear R. (* Martin: There might be other values to clear there. *)
    introv R OR' El FO O0 S0 E1.
    name_heap_write_fields_in eq2 h6.
    asserts OK1sc: (ok_scope h1 sc).
      lets Of: ok_heap_function H1. unfolds in Of.
      rewrite* <- binds_equiv_read in Escope.
      forwards: Of l1.
        left. apply Escope.
      lets (sc'&_&_&_&B'&_&_&OK'): H.
      forwards~: binds_func_scope Escope B'. subst sc'. trivial.
    name_heap_sub_write_fields_in EQh6 h5.
    name_heap_write_in EQh5 h4.
    name_heap_alloc_obj_in EQh4 h3.
    asserts OK6: (ok_heap h6).
      (* This part is very closed to the corresponding one in JsSafety:
         maybe it can be factorized? *)
      asserts: (has_some_proto h3 (fresh_for h0)). subst h3. indom_simpl.
       subst h6.
       apply~ ok_heap_write_fields_user_undef.
         subst h5 h4 h3. apply~ indom_write_fields. indom_simpl.
         apply* fresh_for_spec.
       subst h5. apply~ ok_heap_write_fields_user.
         subst h4 h3. indom_simpl.
         apply* fresh_for_spec.
       subst h4. applys ok_heap_write_this h3 (fresh_for h0) (get_this h1 r1) (@eq_refl).
         subst h3. apply* ok_heap_alloc_obj. constructor.
         apply* fresh_for_spec.
         subst h3. apply* binds_write_neq. apply* binds_write_eq.
         apply* fresh_for_spec.
         applys neq_sym. applys~ fresh_binds_neq h0. apply* fresh_for_spec.
         applys~ ok_heap_special_global_this. apply* O0.
         auto.
       destruct r1 as [v1|[l0 f0]].
         subst h3. do 2 apply* indom_write.
          apply* ok_heap_special_global_proto. apply* O0.
         unfold get_this. case_if.
           subst h3. do 2 apply* indom_write.
            apply* ok_heap_special_global_proto. apply* O0.
           subst h3.
            do 2 apply~ has_some_proto_write. inverts H2 as [N|P].
              subst l0. simpl in eqo. case_if in eqo.
              forwards~: extends_proto_elim E1 P.
       apply* arguments_ok_value. apply* arguments_comp_correct.
       applys~ Forall_trans value (ok_value h0).
         introv Oa. applys~ ok_value_extends h0.
          subst h4 h3. repeat apply* extends_proto_write_trans.
    asserts OKL6: (ok_scope h6 (fresh_for h0 :: sc)).
      subst h6. apply~ ok_scope_write_fields.
      subst h5. apply~ ok_scope_write_fields.
      subst h4. apply~ ok_scope_write.
      subst h3. apply~ ok_scope_cons.
        apply* ok_scope_write.
        apply* ok_scope_extends.
      apply* indom_write_eq.
    forwards [(eq2&nV) | [(r2&h2&eq2&eqv0) | (r2&h2&v2&eq2&eqv0)]]: elim_if_success_value R; tryfalse.
      inverts OR'; tryfalse.
       forwards~ R2: run_prog_correct eq2.
         constructor*.
       forwards~ O': safety_prog R2.
         compute. trivial.
       inverts O'.
       apply~ red_expr_ext_expr_call_3.
         apply* fresh_for_spec.
         apply* arguments_comp_correct.
         apply~ red_expr_ext_expr_prog.
           substs. apply* R2.
           apply~ red_expr_ext_res_prog_res_expr_throw.
         apply~ red_expr_abort.
           constructor~.
      rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
    rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls.
    inverts* R.
    forwards* R2: run_prog_correct eq2.
      constructor*.
    forwards* O2: safety_prog R2.
      compute. trivial.
    applys* red_expr_ext_expr_call_3.
      apply* fresh_for_spec.
      apply* arguments_comp_correct.
      rewrite <- EQh3. rewrite <- EQh4. rewrite <- EQh5.
       unfold reserve_local_vars. rewrite <- EQh6.
         applys~ red_expr_ext_expr_prog R2.
         apply* red_expr_ext_res_prog_res_expr_normal.
      inverts OR'.
      apply~ red_expr_ext_expr_call_4.
        apply* getvalue_comp_correct.
          inverts~ O2.
          inverts~ O2.

  (* unary_op *)
  destruct u.
  (* not *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R; simpl in R; forwards*: wrong_not_ret_expr R.
  rewrite eqv2 in R; simpl in R.
  destruct b'; tryfalse. inverts eqv2.
  inverts~ R.
  forwards~ R': run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R'.
  applys~ red_expr_expr_unary_op R'.
  simpl in OR. inverts OR.
  apply~ red_expr_ext_expr_unary_op_1.
    apply* getvalue_comp_correct.
    apply* unary_op_comp_correct.

  (* delete *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards~ R': run_expr_correct eq1.
    constructors*.
  applys~ red_expr_expr_unary_op R'.
  case_if in R; inverts R.
   simpl in OR. inverts OR.
    apply~ red_expr_ext_expr_unary_op_1_delete_false.
   simpl in OR. inverts OR.
    apply~ red_expr_ext_expr_unary_op_1_delete_true.

  (* typeof *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(v1&eqr) | [(l&f&diffno&eqr) | (f&eqr)]]: elim_if_is_null_ref R.
    rewrite eqr in R. simpl in R.
     forwards [? | (v2&eqv2)]: elim_if_defined R.
       rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
     rewrite eqv2 in R. simpl in R. inverts R.
     forwards~ R1: run_expr_correct eq1.
       constructors*.
     forwards* (OK'&OKL'&OKr1): sub_safety_expr R1.
     forwards~ T: typeof_comp_correct eqv2.
     applys~ red_expr_expr_unary_op R1.
     inverts OR.
     apply* red_expr_ext_expr_unary_op_1_typeof_value.
     subst. apply~ getvalue_value.
    rewrite eqr in R. simpl in R. case_if in R.
     forwards [? | (v2&eqv2)]: elim_if_defined R.
       rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
     rewrite eqv2 in R. simpl in R.
     destruct f; tryfalse.
     forwards [? | (v3&eqv3)]: elim_if_defined R.
       rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
     rewrite eqv3 in R. simpl in R. inverts R.
     forwards~ R1: run_expr_correct eq1.
       constructors*.
     forwards* (OK'&OKL'&OKr1): sub_safety_expr R1.
     forwards~ T: typeof_comp_correct eqv3.
     applys~ red_expr_expr_unary_op R1.
     inverts OR.
     apply* red_expr_ext_expr_unary_op_1_typeof_value.
     apply* getvalue_comp_correct. rewrite eqr. simpl. apply~ eqv2.
    rewrite eqr in R. simpl in R. case_if in R. inverts R.
     forwards~ R1: run_expr_correct eq1.
       constructors*.
     forwards* (OK'&OKL'&OKr1): sub_safety_expr R1.
     subst. inverts~ OKr1.
     applys~ red_expr_expr_unary_op R1.
     inverts OR.
     apply red_expr_ext_expr_unary_op_1_typeof_undefined.

  (* The next four cases are similar *)
  (* pre_incr *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  case_if in eqv1.
  case_if in eqv1. inverts eqv1. rewrite~ binary_op_comp_fix in eqv2. inverts eqv2.
  forwards~ R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
  applys~ red_expr_expr_unary_op R1.
  inverts OR.
  apply* red_expr_ext_expr_unary_op_1_pre_incr.
    apply* getvalue_comp_correct.
      inverts eqv1. simpl. repeat case_if*.
    apply* binary_op_comp_correct.
      rewrite~ binary_op_comp_fix.
      rewrite~ binary_op_comp_fix in eqv2. inverts~ eqv1.
      inverts~ eqv1.

  (* post_incr *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  case_if in eqv1.
  case_if in eqv1. inverts eqv1. rewrite~ binary_op_comp_fix in eqv2. inverts eqv2.
  forwards~ R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
  applys~ red_expr_expr_unary_op R1.
  inverts OR.
  apply* red_expr_ext_expr_unary_op_1_post_incr.
    apply* getvalue_comp_correct.
      inverts eqv1. simpl. repeat case_if*.
    apply* binary_op_comp_correct.
      rewrite~ binary_op_comp_fix.
      rewrite~ binary_op_comp_fix in eqv2.

  (* pre_decr *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  case_if in eqv1.
  case_if in eqv1. inverts eqv1. rewrite~ binary_op_comp_fix in eqv2. inverts eqv2.
  forwards~ R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
  applys~ red_expr_expr_unary_op R1.
  inverts OR.
  apply* red_expr_ext_expr_unary_op_1_pre_decr.
    apply* getvalue_comp_correct.
      inverts eqv1. simpl. repeat case_if*.
    apply* binary_op_comp_correct.
      rewrite~ binary_op_comp_fix.
      rewrite~ binary_op_comp_fix in eqv2. inverts~ eqv1.
      inverts~ eqv1.

  (* post_decr *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  destruct f; tryfalse.
  rewrite eqv1 in R. simpl in R.
  forwards [? | (v2&eqv2)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv2 in R. simpl in R.
  inverts R. substs.
  case_if in eqv1.
  case_if in eqv1. inverts eqv1. rewrite~ binary_op_comp_fix in eqv2. inverts eqv2.
  forwards~ R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  asserts OV1: (ok_value h1 v1).
    repeat case_if in eqv1; inverts eqv1.
    lets OKV: ok_heap_ok_value OK1. unfolds in OKV.
    apply* OKV. rewrite* binds_equiv_read.
      apply* proto_indom. apply* proto_comp_correct.
        inverts~ OKr1. inverts* H0.
        apply* indom_bound.
      auto*.
  asserts OKV1': (ok_value h v1).
    inverts* OV1.
    rewrite~ binary_op_comp_fix in eqv2. simpl in eqv2.
    false eqv2.
  applys~ red_expr_expr_unary_op R1.
  inverts OR.
  apply* red_expr_ext_expr_unary_op_1_post_decr.
    apply* getvalue_comp_correct.
      inverts eqv1. simpl. repeat case_if*.
    apply* binary_op_comp_correct.
      rewrite~ binary_op_comp_fix.
      rewrite~ binary_op_comp_fix in eqv2.

  (* void *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_unary_op R1.
     apply~ red_expr_abort.
     inverts OR; tryfalse.
     constructors~.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  inverts~ R.
  forwards~ R': run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R'.
  applys~ red_expr_expr_unary_op R'.
  inverts OR.
  apply~ red_expr_ext_expr_unary_op_1.
    apply* getvalue_comp_correct.
    apply* unary_op_comp_correct.

  (* binary_op *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_binary_op R1.
     inverts OR; tryfalse.
     apply~ red_expr_abort.
     constructors~.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  apply* red_expr_expr_binary_op.
  forwards* He1: run_expr_correct eq1.
    constructors*.
  forwards* (O1&OL1&Or1): sub_safety_expr He1.
  forwards* G0: getvalue_comp_correct eqv0.
  apply* red_expr_ext_expr_binary_op_1.
  apply* lazy_binary_op_comp_correct.
  forwards [? | (v'&eqv')]: elim_if_defined_else R.
   rewrite H in R. simpl in R.
    forwards [(eq2&nV) | [(v1&h2&eq2&eqv1) | (v1&h2&b''&eq2&eqv1)]]: elim_if_success_value R; tryfalse.
      forwards* R2: run_expr_correct eq2.
       inverts OR; tryfalse. rewrite H. simpl.
       applys~ red_expr_ext_expr_binary_op_2_none R2.
       apply~ red_expr_abort.
       constructors~.
      rewrite eq2 in R. simpls. rewrite eqv1 in R. simpls. forwards*: wrong_not_ret_expr R.
    rewrite eq2 in R. simpls. rewrite eqv1 in R. simpls.
    forwards [? | (v3&eqv3)]: elim_if_defined R.
      rewrite H0 in R. simpl in R. forwards*: wrong_not_ret_expr R.
    rewrite eqv3 in R. simpl in R.
    inverts* R.
    forwards* R2: run_expr_correct eq2.
      constructors*.
    forwards* O2: safety_expr R2.
      constructors~.
    forwards* G1: getvalue_comp_correct eqv1.
      inverts~ O2.
      inverts~ O2.
    inverts OR.
    rewrite H. simpl. apply* red_expr_ext_expr_binary_op_2_none.
    apply* red_expr_ext_expr_binary_op_3.
    apply* binary_op_comp_correct.
    inverts~ O2.
    applys* ok_value_extends h1. forwards* O0: ok_ret_expr_prove G0.
      inverts~ O0.
      inverts~ O2.
      apply* getvalue_ok_value.
      forwards* OKr1: ok_ret_expr_prove G1; inverts~ O2.
      inverts~ O2.
  rewrite eqv' in * |- *. simpls.
  inverts R. inverts OR.
  apply* red_expr_ext_expr_binary_op_2_some.

  (* assign *)
  destruct o.
  (* with an operator *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_expr_correct eq1.
     applys~ red_expr_expr_assign R1.
     inverts OR; tryfalse.
     apply~ red_expr_abort.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards [? | (v1&eqv1)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv1 in R. simpl in R.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* O1: safety_expr R1.
    compute. trivial.
  inverts O1.
  forwards~ OL1: ok_scope_extends h h1 s.
  apply* red_expr_expr_assign.
  forwards [(eq2&nV) | [(r2&h2&eq2&eqv2) | (r2&h2&v2&eq2&eqv2)]]: elim_if_success_value R; tryfalse.
    forwards* R2: run_expr_correct eq2.
     inverts OR; tryfalse. subst r1.
     applys~ red_expr_ext_expr_assign_1_op R2.
       apply* getvalue_comp_correct.
     apply~ red_expr_abort.
     constructors~.
    rewrite eq2 in R. simpls. rewrite eqv2 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq2 in R. simpls. rewrite eqv2 in R. simpls.
  destruct f; tryfalse.
  subst r1.
  forwards [? | (v3&eqv3)]: elim_if_defined R.
    rewrite H in R. simpl in R. forwards*: wrong_not_ret_expr R.
  rewrite eqv3 in R. simpl in R.
  inverts R.
  forwards~ R2: run_expr_correct eq2.
    constructors*.
  forwards~ O2: safety_expr R2.
    compute. trivial.
  apply~ red_expr_ext_expr_assign_1_op.
    apply* getvalue_comp_correct.
    apply* R2.
  inverts OR.
  apply~ red_expr_ext_expr_assign_2_op.
    apply* getvalue_comp_correct.
    inverts~ O2.
    inverts~ O2.
    apply* binary_op_comp_correct.
      inverts~ O2.
      applys~ ok_value_extends h1.
       case_if in eqv1. case_if in eqv1.
       inverts* eqv1.
       inverts* eqv1. apply* ok_heap_ok_value.
         rewrite* binds_equiv_read.
          apply* proto_indom.
          apply* proto_comp_correct.
          apply* indom_bound.
          inverts H2.
          inverts* H0.
          splits; discriminate.
         inverts~ O2.
      inverts~ O2. inverts~ H5.
       simpls. inverts~ eqv2.
       simpls. inverts~ eqv2.
       case_if in H5. case_if in H5.
        inverts~ H5.
        inverts~ H5. apply* ok_heap_ok_value.
          rewrite* binds_equiv_read.
           apply~ proto_indom.
           apply* proto_comp_correct.
           apply* indom_bound.
          splits; discriminate.
  (* without *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
   forwards* R1: run_expr_correct eq1.
    applys~ red_expr_expr_assign R1.
    inverts OR; tryfalse.
    apply~ red_expr_abort.
    constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [(eqw&v'&eqv') | (l&f&eq')]: elim_if_is_ref R.
    lets (h'0&eqw'): eqw. forwards*: wrong_not_ret_expr eqw'.
  rewrite eq' in R. simpl in R.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  inverts* OKr1; tryfalse. inverts H0.
  apply* red_expr_expr_assign.
  forwards [(eq2&nV) | [(v0&h2&eq2&eqv0) | (v0&h2&b&eq2&eqv0)]]: elim_if_success_value R; tryfalse.
    forwards* R2: run_expr_correct eq2.
     inverts OR; tryfalse.
     applys~ red_expr_ext_expr_assign_1 R2.
     apply~ red_expr_abort.
     constructors~.
    rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq2 in R. simpls. rewrite eqv0 in R. simpls.
  inverts* R.
  forwards* R2: run_expr_correct eq2.
    constructors*.
  forwards* (OK2&OKL2&OKr2): sub_safety_expr R2.
  apply* red_expr_ext_expr_assign_1.
  inverts OR.
  apply* red_expr_ext_expr_assign_2_normal.
  apply* getvalue_comp_correct.

  (* run_stat *)
  introv R OR OK OKL. destruct p; simpl in R;
    try (inverts* R; fail).

  (* expr *)
  forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
  forwards* Re: run_expr_correct R.
  apply~ red_stat_stat_expr.
  apply* red_stat_ext_stat_expr.

  (* seq *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_stat_correct eq1.
     applys~ red_stat_stat_seq R1.
     inverts OR; tryfalse.
     apply~ red_stat_abort.
       intro A. inverts A.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards~ R1: run_stat_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_stat R1.
  apply* red_stat_stat_seq.
  forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
    forwards* R2: run_stat_correct eq2.
     applys~ red_stat_ext_stat_seq_1 R2.
  rewrite eq2 in R. simpl in R.
  inverts* R.
  forwards~ R2: run_stat_correct eq2.
    constructors*.
  forwards* (OK2&OKL2&OKr2): sub_safety_stat R2.
  inverts OR.
  apply* red_stat_ext_stat_seq_1.

  (* var_decl *)
  destruct o.
   (* with expression *)
   forwards [(eq1&nV) | (v0&h0&eq)]: elim_if_success R; tryfalse.
     forwards* R1: run_stat_correct eq1.
      inverts R1.
       apply~ red_stat_abort.
        intro A. inverts A.
      applys~ red_stat_stat_var_decl_expr H2.
      inverts OR; tryfalse.
      apply~ red_stat_abort.
        intro A. inverts A.
      constructors~.
    rewrite eq in R. simpl in R.
    inverts R.
    forwards~ R1: run_stat_correct eq.
      constructors*.
    name_out_prog_ter R1 o.
    applys~ red_stat_stat_var_decl_expr o.
      inverts~ R1.
      simpl in H. inverts H.
    inverts~ R1.
      simpl in H. inverts H.
    subst. inverts OR. apply~ red_stat_ext_stat_var_decl_expr_1.
   (* without *)
   inverts R.
   inverts OR.
   apply~ red_stat_stat_var_decl.

  (* if *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
   forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
    forwards~ R1: run_expr_correct eq1 OR'.
    forwards* O1: safety_expr R1.
      compute. trivial.
    name_out_expr_ter R1 o1.
    applys~ red_stat_stat_if (out_prog_ter h' re).
      applys~ red_stat_ext_stat_expr R1.
      subst. apply* SOR.
    apply~ red_stat_abort.
      intro A. inverts A.
    inverts OR; tryfalse.
    constructors~.
   rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
    forwards*: wrong_not_ret_expr R.
   rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
    forwards~ R1: run_expr_correct eq1.
      constructors*.
    forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
    name_out_expr_ter R1 o1.
    applys~ red_stat_stat_if (out_prog_ter h1 v0).
      applys~ red_stat_ext_stat_expr R1.
      subst. apply~ red_stat_ext_res_expr_res_prog_normal.
    forwards~ G: getvalue_comp_correct eqv0.
    forwards [(?&?) | [eqv | eqv]]: elim_if_boolean R.
      forwards*: ret_not_wrong_expr H.
      subst. simpl in R.
       forwards~ R2: run_stat_correct R.
         apply* OR.
       inverts OR.
        apply* red_stat_ext_stat_if_1_true.
        inverts OR'.
        apply* red_stat_ext_stat_if_1_true.
      subst. simpl in R. destruct o.
       forwards~ R2: run_stat_correct R.
         apply* OR.
        apply* red_stat_ext_stat_if_1_false.
       inverts R. inverts OR.
        apply* red_stat_ext_stat_if_1_false_implicit.

  (* while *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     forwards~ R1: run_expr_correct eq1 OR'.
     forwards* O1: safety_expr R1.
       compute. trivial.
     name_out_expr_ter R1 o1.
     applys~ red_stat_stat_while (out_prog_ter h' re).
       applys~ red_stat_ext_stat_expr R1.
       subst. apply* SOR.
     apply~ red_stat_abort.
       intro A. inverts A.
     inverts OR; tryfalse.
     constructors~.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls. forwards*: wrong_not_ret_expr R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
  forwards~ R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  name_out_expr_ter R1 o.
  applys~ red_stat_stat_while (out_prog_ter h1 v0).
    applys~ red_stat_ext_stat_expr R1.
    subst. apply~ red_stat_ext_res_expr_res_prog_normal.
  forwards~ G: getvalue_comp_correct eqv0.
  forwards [(?&?) | [eqv | eqv]]: elim_if_boolean R.
    forwards*: ret_not_wrong_expr H.
   subst b'. simpls.
    forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
      forwards* R2: run_stat_correct eq2.
       inverts OR; tryfalse.
       applys~ red_stat_ext_stat_while_1_true R2.
         apply* G.
       apply~ red_stat_abort.
         intro A. inverts A.
         constructors~.
    rewrite eq2 in R. simpl in R.
    forwards~ R2: run_stat_correct eq2.
      constructors*.
    forwards* (OK2&OKL2&OKr2): sub_safety_stat R2.
    forwards~ R3: run_stat_correct R.
      apply* OR.
    inverts R. apply* red_stat_ext_stat_while_1_true.
    apply~ red_stat_ext_stat_while_2.
   subst b'. simpls.
    inverts R. inverts OR. apply* red_stat_ext_stat_while_1_false.

  (* with *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     forwards~ R1: run_expr_correct eq1 OR'.
     forwards* O1: safety_expr R1.
       compute. trivial.
     name_out_expr_ter R1 o1.
     applys~ red_stat_stat_with (out_prog_ter h' re).
       applys~ red_stat_ext_stat_expr R1.
       subst. apply* SOR.
     apply~ red_stat_abort.
       intro A. inverts A.
     inverts OR; tryfalse.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards [eqr | [(eqr&v'&eqo) | (l&eqo&diffno)]]: elim_if_not_eq R.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     rewrite eqr in R. simpl in R. forwards*: wrong_not_ret_expr R.
    forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     lets (h'0&eqr'): eqr. forwards*: wrong_not_ret_expr eqr'.
  rewrite eqo in R. simpl in R.
  case_if in R.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  asserts OL1: (ok_scope h1 (l :: s)).
    apply* ok_scope_cons.
    assert (ok_value h1 l).
      inverts OKr1; simpls.
      inverts* eqo.
      inverts H;
        case_if* in eqo; tryfalse.
      case_if* in eqo;
        tryfalse.
      inverts eqo.
      lets OKV1: ok_heap_ok_value OK1.
      unfold ok_heap_ok_value_def in OKV1.
      apply~ OKV1.
        rewrite* binds_equiv_read.
         apply* proto_indom.
         apply* proto_comp_correct.
         apply* indom_bound.
        split; discriminate.
    inverts* H.
  name_out_expr_ter R1 o.
  applys~ red_stat_stat_with (out_prog_ter h1 r1).
    applys~ red_stat_ext_stat_expr R1.
    subst. apply~ red_stat_ext_res_expr_res_prog_normal.
  forwards~ G: getvalue_comp_correct eqo.
  forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
    forwards* R2: run_stat_correct eq2.
     inverts OR; tryfalse.
     applys~ red_stat_ext_stat_with_1 R2.
  rewrite eq2 in R. simpl in R.
  inverts* R.
  forwards* R2: run_stat_correct eq2.
  apply* red_stat_ext_stat_with_1.

  (* throw *)
  forwards [(eq1&nV) | [(v0&h1&eq1&eqv0) | (v0&h1&b'&eq1&eqv0)]]: elim_if_success_value R; tryfalse.
    inverts OR; tryfalse.
     forwards* R1: run_expr_correct eq1.
       constructors*.
     apply~ red_stat_stat_throw.
       applys~ red_stat_ext_stat_expr R1.
       apply* red_stat_ext_res_expr_res_prog_throw.
     apply~ red_stat_abort.
       intro A. inverts A.
       constructors~.
    rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
     forwards~ (re'&OR'&SOR): stat_ret_res_expr_to_prog OR.
     forwards*: wrong_not_ret_expr R.
  rewrite eq1 in R. simpls. rewrite eqv0 in R. simpls.
  inverts R. inverts OR.
  forwards* R1: run_expr_correct eq1.
    constructors*.
  forwards* (OK1&OKL1&OKr1): sub_safety_expr R1.
  apply~ red_stat_stat_throw.
    applys~ red_stat_ext_stat_expr R1.
    apply* red_stat_ext_res_expr_res_prog_normal.
  apply~ red_stat_ext_stat_throw_1.
    apply* getvalue_comp_correct.

  (* try *)
  forwards [(eq1&nV1&nV2) | [(r0&h1&eq1) | (v0&h1&eq1)]]: elim_if_success_or_throw R; tryfalse.
    inverts OR; tryfalse.
    rewrite eq1 in R. simpls.
     forwards~ R1: run_stat_correct eq1.
       constructors*.
     forwards~ O1: safety_stat R1.
       compute. trivial.
     inverts O1.
     applys~ red_stat_stat_try R1.
     apply~ red_stat_ext_stat_try_1_finally.
       intro A. inverts~ A.
     destruct~ o0.
      forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
        inverts OR; tryfalse.
         forwards* R2: run_stat_correct eq2.
           constructors*.
           applys~ ok_scope_extends h.
         applys~ red_stat_ext_stat_try_3_some R2.
         apply~ red_stat_abort.
           intro A. inverts A.
           constructors~.
       rewrite eq2 in R. simpl in R.
       inverts R.
       forwards~ R2: run_stat_correct eq2.
         constructors*.
         applys~ ok_scope_extends h.
       applys~ red_stat_ext_stat_try_3_some R2.
       inverts OR.
       apply* red_stat_ext_stat_try_4_normal.
      inverts R. inverts OR.
       apply* red_stat_ext_stat_try_3_none.
   rewrite eq1 in R. simpl in R.
    forwards~ R1: run_stat_correct eq1.
      constructors*.
    forwards~ O1: safety_stat R1.
      compute. trivial.
    inverts O1.
    applys~ red_stat_stat_try R1.
    destruct o.
     destruct c as (x&s1). apply~ red_stat_ext_stat_try_1_catch.
       apply* fresh_for_spec.
       name_heap_write_in R h2.
        name_heap_alloc_obj_in EQh2 h3.
       sets_eq <- runS: (run_stat m h2 (fresh_for h1 :: s) s1).
        asserts (h4&r4&eq): (exists h1 r1, runS = out_return h1 r1).
          destruct runS; destruct o0; inverts* R.
        rewrite eq in R. rewrite eq in EQrunS. clear eq.
        asserts (re4&Hre4): (exists re, ret_res_prog r4 re).
          destruct r4.
           exists r0. constructors*.
           eexists. constructors*.
           false. destruct o0.
            inverts R. inverts OR.
            inverts R. inverts OR.
        asserts O3: (ok_heap h3). substs.
          asserts (vop&Hvop): (exists vop, binds h1 loc_obj_proto field_proto vop).
            inverts H1. inverts ok_heap_special. apply* indom_binds.
          apply~ ok_heap_alloc_obj.
            applys~ ok_heap_protochain Hvop.
            right. apply* binds_indom.
            apply* fresh_for_spec.
        asserts O2: (ok_heap h2).
           substs. apply~ ok_heap_write_user.
             applys~ ok_value_extends h1.
             apply* extends_proto_write.
            indom_simpl.
            apply* fresh_for_spec.
        asserts OL: (ok_scope h2 (fresh_for h1 :: s)).
          applys~ ok_scope_cons.
           applys~ ok_scope_extends h1.
            applys~ ok_scope_extends h.
            subst h2. applys~ extends_proto_trans h3.
             substs. apply* extends_proto_write.
           substs. indom_simpl.
        forwards* R2: run_stat_correct EQrunS.
        applys~ red_stat_ext_stat_try_2 R2.
        forwards* O4: safety_stat R2.
          compute. trivial.
        destruct o0.
         asserts R': (if_success (run_stat m h4 s s0)
           (fun h' _ => out_return h' r4) = out_return h' r).
           destruct r4; inverts~ Hre4. clear R.
          asserts OK4: (ok_heap h4).
            inverts~ O4.
          asserts OL4: (ok_scope h4 s).
            applys~ ok_scope_extends h.
            applys~ extends_proto_trans h2.
             applys~ extends_proto_trans h3.
              applys~ extends_proto_trans h1.
              substs. apply~ extends_proto_write.
             substs. apply~ extends_proto_write.
            inverts~ O4.
          forwards [(eq2&nV') | (r5&h5&eq5)]: elim_if_success R'; tryfalse.
            forwards* R3: run_stat_correct eq2.
             applys~ red_stat_ext_stat_try_3_some R3.
             inverts OR; tryfalse.
             apply~ red_stat_abort.
               intro A. inverts A.
               constructors~.
            rewrite eq5 in R'. simpl in R'. inverts R'.
             forwards* R3: run_stat_correct eq5.
               constructors*.
             applys~ red_stat_ext_stat_try_3_some R3.
             asserts: (re4 = re).
               inverts OR; inverts~ Hre4.
             subst re4.
             apply red_stat_ext_stat_try_4_normal.
         inverts R.
          asserts: (re4 = re).
            inverts OR; inverts~ Hre4.
          subst re4.
          apply~ red_stat_ext_stat_try_3_none.
     apply~ red_stat_ext_stat_try_1_no_catch.
      asserts OL1: (ok_scope h1 s).
        applys~ ok_scope_extends OKL.
      destruct o0.
       forwards [(eq2&nV2) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
         forwards* R2: run_stat_correct eq2.
          applys~ red_stat_ext_stat_try_3_some R2.
          inverts OR; tryfalse.
          apply~ red_stat_abort.
            intro A. inverts A.
            constructors~.
         forwards* R2: run_stat_correct eq2.
           constructors*.
          applys~ red_stat_ext_stat_try_3_some R2.
          rewrite eq2 in R. simpl in R. inverts R.
          inverts OR.
          apply~ red_stat_ext_stat_try_4_normal.
       inverts R. inverts OR.
        apply~ red_stat_ext_stat_try_3_none.

  (* skip *)
  inverts R. inverts OR.
  apply* red_stat_stat_skip.

  (* run_prog *)
  introv R OR OK OKL. destruct P; simpl in R;
    try (inverts* R; fail).

  (* stat *)
  apply* red_prog_prog_stat.

  (* seq *)
  forwards [(eq1&nV) | (r1&h1&eq1)]: elim_if_success R; tryfalse.
    forwards* R1: run_prog_correct eq1.
     applys~ red_prog_prog_seq R1.
     inverts~ OR; tryfalse.
     apply~ red_prog_abort.
     constructors~.
  rewrite eq1 in R. simpl in R.
  forwards~ R1: run_prog_correct eq1.
    constructors*.
  forwards~ O1: safety_prog R1.
   compute. trivial.
  inverts~ O1.
  applys~ red_prog_prog_seq R1.
  asserts S1: (ok_scope h1 s).
    applys~ ok_scope_extends h.
  forwards [(eq2&nV) | (r2&h2&eq2)]: elim_if_success R; tryfalse.
    forwards* R2: run_prog_correct eq2.
     applys~ red_prog_ext_prog_seq_1 R2.
  rewrite eq2 in R. simpl in R.
  inverts R. inverts OR.
  forwards~ R2: run_prog_correct eq2.
    constructors*.
  applys~ red_prog_ext_prog_seq_1 R2.

  (* run_list_expr_correct_aux *)
  introv Eq OR F FO Oh Os.
   induction le.
    simpl in Eq. rewrite rev_rev in Eq.
     inverts OR; tryfalse.
      apply~ red_expr_ext_list_then_1_nil.
      apply* F.
      constructors*.
      apply~ red_expr_ext_list_then_1_nil.
      applys* F.
      constructors*.
   simpl in Eq.
    forwards [(eq2&nV) | [(v0&h2&eq2&eqv0) | (v0&h2&b&eq2&eqv0)]]: elim_if_success_value Eq; tryfalse.
      inverts OR; tryfalse.
       forwards~ R2: run_expr_correct eq2.
         constructors*.
       forwards~ O': safety_expr R2.
         compute. trivial.
       inverts O'.
       applys~ red_expr_ext_list_then_1_cons R2.
       apply~ red_expr_abort.
         constructors~.
      rewrite eq2 in Eq. simpls. rewrite eqv0 in Eq. simpls. forwards*: wrong_not_ret_expr Eq.
    rewrite eq2 in Eq. simpls. rewrite eqv0 in Eq. simpls.
    forwards~ Re: run_expr_correct eq2.
      constructors*.
    applys~ red_expr_ext_list_then_1_cons Re.
    forwards* S2: safety_expr Re.
      compute. trivial.
    inverts~ S2.
    forwards~ Gb: getvalue_comp_correct eqv0.
    applys~ red_expr_ext_list_then_2 Gb.
    rewrite <- rev_last in Eq.
    applys~ run_list_expr_correct_aux Eq.
     rewrite length_last. rewrite length_cons in F.
      introv ? ? E ? ? ? Ex. apply* F. rewrite E. auto with zarith.
      applys~ extends_proto_trans h2.
     apply* Forall_last.
      applys~ Forall_trans FO.
       introv O. applys~ ok_value_extends O.
      apply* getvalue_ok_value.
     apply* ok_scope_extends.

Qed.

Theorem run_expr_correct : forall m, run_expr_correct_def m.
Proof. apply* run_correct_aux. Qed.

Theorem run_stat_correct : forall m, run_stat_correct_def m.
Proof. apply* run_correct_aux. Qed.

Theorem run_prog_correct : forall m, run_prog_correct_def m.
Proof. apply* run_correct_aux. Qed.

(* Require a deterministic semantic:
Theorem run_complete : forall h h' L e v,
  red h L e h' v ->
  ok_heap h -> ok_scope h L ->
  exists m, run m h L e = out_return h' (ret_ret_expr v).
*)

End Correctness.

