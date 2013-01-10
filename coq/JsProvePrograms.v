(* This file contains lemmas and definition that could eventualy be useful to prove programs. *)

Set Implicit Arguments.
Require Import Shared JsSemanticsAux JsWf JsWfAux JsSafety JsScopes.
Require Import Wf Wellfounded Recdef LibFix.


Section Utils.

Inductive AllBefore {A : Type} (P : A -> Prop) : A -> list A -> Prop :=
  | AllBefore_init : forall l L, AllBefore P l (l :: L)
  | AllBefore_constr : forall l L a, a <> l -> AllBefore P l L -> P a -> AllBefore P l (a :: L).

Lemma AllBefore_destr {A : Type} :
  forall (a : A) b l P,
  a <> b ->
  AllBefore P a (b :: l) ->
  AllBefore P a l.
Proof.
introv D AB.
inversion AB; subst~; tryfalse.
Qed.

End Utils.

Section In_protochain.
Inductive in_protochain : heap -> field -> loc -> loc -> Prop :=
  | in_protochain_here : forall h l f, in_protochain h f l l
  | in_protochain_next : forall h l f l' l'',
    ~ indom h l f ->
    binds h l field_proto (value_loc l') ->
    in_protochain h f l' l'' -> in_protochain h f l l''.

(* This predicate is useful to reason about the size of a proto chain without considering its heap:
  it would be nice to only reason on the size of a reduction. *)
Inductive protochain_long : nat -> heap -> field -> loc -> loc -> Prop :=
    protochain_long_here : forall (h : heap) (l : loc) (f : field),
                          protochain_long 0 h f l l
  | protochain_long_next : forall (h : heap) (l : loc) (f : field) (l' l'' : loc) n,
                          ~ indom h l f ->
                          binds h l field_proto (value_loc l') ->
                          protochain_long n h f l' l'' ->
                          protochain_long (S n) h f l l''.

Lemma protochain_long_compose :
  forall n1 n2 h f l1 l2 l3,
  protochain_long n1 h f l1 l2 ->
  protochain_long n2 h f l2 l3 ->
  protochain_long (n1 + n2) h f l1 l3.
Proof.
introv PC; induction PC; intro PC'; simpl; auto.
applys* protochain_long_next l'.
Qed.

Lemma in_protochain_impl_in_protochain_long :
  forall h f l1 l2,
  in_protochain h f l1 l2 ->
  exists n, protochain_long n h f l1 l2.
Proof.
introv IPC; induction IPC.
  exists 0%nat.
  constructor.
lets (x & H1): IHIPC.
exists (S x).
applys* protochain_long_next l'.
Qed.

End In_protochain.

Section Loops.

Lemma non_direct_cyclic_proto h :
  ok_heap h ->
  forall l, ~ binds h l field_proto (value_loc l).
Proof.
intro OK; inversion OK.
unfold ok_heap_protochain_def. introv B.
assert (~protochain h l) as NP.
  intro PC; induction PC.
    forwards*: ok_heap_null.
  forwards~: binds_func_loc B H; subst.
  apply~ IHPC.
apply NP.
apply* ok_heap_protochain.
Qed.

Lemma in_protochain_null_eq_null :
  forall h f l,
  ok_heap h ->
  in_protochain h f loc_null l ->
  l = loc_null.
Proof.
introv OK IPC; inversion IPC; subst~.
forwards*: ok_heap_null. false*.
Qed.

Lemma protochain_long_non_loop :
  forall h f l n,
  ok_heap h ->
  ~protochain_long (S n) h f l l.
Proof.
introv WF pcl.

assert (protochain h l) as H.
  destruct WF.
  unfold ok_heap_protochain_def. inversion pcl; subst.
  apply ok_heap_protochain in H1.
  auto.

induction H.
  inversion pcl; subst.
  forwards*: ok_heap_null H1.

apply~ IHprotochain.
inversion pcl; subst.
forwards~: binds_func_loc H H3; subst.

change (protochain_long (1 + n) h f l'0 l'0).
rewrite plus_comm.
applys* protochain_long_compose l.

applys* protochain_long_next l'0.

constructor.
Qed.

Lemma non_cyclic_proto h :
  ok_heap h ->
  forall l l' f,
  l <> l' ->
  in_protochain h f l l' ->
  in_protochain h f l' l ->
  False.
Proof.
introv WF D ipc1 ipc2.

apply in_protochain_impl_in_protochain_long in ipc1.
apply in_protochain_impl_in_protochain_long in ipc2.
lets (n1 & ipc1'): ipc1.
lets (n2 & ipc2'): ipc2.

destruct n1.
  inversion ipc1'; subst; apply D; reflexivity.

assert (protochain_long ((S n1) + n2) h f l l).
  applys* protochain_long_compose l'.
simpl in H.

forwards*: protochain_long_non_loop H.
Qed.

End Loops.

Section ProtoChain. (* Computing the length of a proto chain (can be useful to evaluate computation time). *)

Definition in_protochain_strict h f l2 l1 := (* Warning, it's inversed (otherwise it won't be well founded). *)
  l1 <> l2 /\ in_protochain h f l1 l2.

Lemma wf_in_protochain_strict :
  forall (H : {h : heap | ok_heap h}) (f : field), well_founded (in_protochain_strict (proj1_sig H) f).
Proof.
introv.
lets (h & WF): H.
unfold well_founded.
constructor.
introv H0.
inverts H0.
assert (protochain h a).
  inverts keep WF.
  unfold ok_heap_protochain_def. inverts* H2.
gen y; induction H0; intros.
  forwards*: in_protochain_null_eq_null.
  subst; false~ H1.
tests: (y = l').
  subst.
  constructor.
  introv (? & ?).
  apply~ IHprotochain.
apply~ IHprotochain.
inverts* H3.
forwards: binds_func_loc H5 H0.
subst~.
Qed.

Tactic Notation "clean_refl" :=
  rew_refl in *; fold_bool; rew_refl in *.

(* TODO:  Use an optimal fixpoint there. *)
Function protochain_length (H : {h | ok_heap h}) (f : field) (l : loc)
  {wf (in_protochain_strict (proj1_sig H) f) l} : nat :=
  let h := proj1_sig H in
  ifb l = loc_null then 0%nat
  else ifb indom h l f then 0%nat
  else ifb indom h l field_proto then (
    match read h l field_proto with
    | value_loc l' => S (protochain_length H f l')
    | _ => 0%nat (* This never happens. *)
    end
  ) else 0%nat.
Proof.
2: apply wf_in_protochain_strict.
intros.
destruct H as (h & ?); simpls.
clean_refl.
split.

intro; subst.
rewrite <- binds_equiv_read in teq2.
applys* non_direct_cyclic_proto teq2.
eauto.

applys* in_protochain_next l'.
  assert (indom h l field_proto). (* anonymous1 is used in an other property. *)
    eauto.
  rewrite indom_equiv_binds in H.
  lets (v & H'): H.
  assert (v = value_loc l').
    rewrite <- binds_equiv_read in teq2.
    apply* binds_func.
    rewrite indom_equiv_binds.
    eauto.
  subst~.

constructor.
Qed.

(*
  There is a warning (`cannot define graph(s)'), but the following extraction works as wanted:
  Extraction protochain_length_terminate.
*)

Lemma protochain_length_correct :
  forall H f l n l',
  n = protochain_length H f l ->
  proto (proj1_sig H) f l l' ->
  protochain_long n (proj1_sig H) f l l'.
Proof.
introv H0 H1.
symmetry in H0.
destruct H as [h ok]; simpls.
gen n; induction H1; intros.
assert (n = 0%nat); [idtac | clear H0; subst; constructor].
 rewrite protochain_length_equation in H0; simpl in H0.
 case_if*.

rewrite protochain_length_equation in H0; simpl in H0.
case_if*.
  subst.
  constructor.
case_if*.
  subst.
  constructor.

rewrite protochain_length_equation in H2; simpl in H2.
cases_if*.
  subst. false* ok_heap_null.
case_if*.
case_if*.
rewrite binds_equiv_read in H0; auto.
rewrite H0 in H2; simpl in H2.
subst.
applys* protochain_long_next l'.
  rewrite~ binds_equiv_read.
false n2; rewrite* indom_equiv_binds.
Qed.

Lemma protochain_long_unique :
  forall h l0 l1 f n1 n2,
  ok_heap h ->
  protochain_long n1 h f l0 l1 ->
  protochain_long n2 h f l0 l1 ->
  n1 = n2.
Proof.
introv OK; inversion OK.
unfold ok_heap_protochain_def.
gen n2 l0 l1; induction n1; introv.
  subst; inversion 1; subst.
  destruct~ n2.
  intro H0; forwards*: protochain_long_non_loop h f l1 n2; false*.

intro H; inversion H; subst.
destruct n2.
  intro H0; inversion H0; subst.
  apply protochain_long_non_loop in H; auto.
    false.

intro H4; inversion H4; subst.

assert (n1 = n2); [idtac | subst~].

assert (l' = l'0); [idtac | subst].
  applys* binds_func_loc h field_proto l0.

apply* IHn1.
Qed.

Lemma in_protochain_write_end :
  forall h f a l v,
  in_protochain (write h l f v) f a l -> in_protochain h f a l.
Proof.
introv IPC.
assert (forall h0 : heap, h0 = write h l f v -> in_protochain h f a l) as H; [idtac | apply~ H].

introv E.
rewrite <- E in IPC.
induction IPC.
  constructor.
applys* in_protochain_next l'.
subst.
tests: (l = l''); subst.
  false H.
  apply~ indom_write_eq.
intro I; apply H.
apply~ indom_write.

subst.
tests: (l = l''); subst.
  false H.
  apply~ indom_write_eq.
apply* binds_write_neq_inv.
Qed.

Lemma in_protochain_write_end_inv :
  forall h f l l' f' v,
  in_protochain h f l l' ->
  in_protochain (write h l' f' v) f l l'.
Proof.
introv.
tests: (l = l'); subst.
  constructor.
intro H; induction H.
  constructor.
applys in_protochain_next l'.
  intro; false H.
  applys* indom_write_inv l'' f' v.
apply~ binds_write_neq.
tests: (l' = l''); subst.
  constructor.
apply~ IHin_protochain.
Qed.

Lemma not_in_protochain_conserve_proto :
  forall h f l l' a v,
  ~in_protochain h f l l' ->
  proto h f l a ->
  proto (write h l' f v) f l a.
Proof.
introv H H0.
gen H.
induction H0.
  constructor.
  constructor.
  apply~ indom_write.
intro H2; applys proto_next l'0.
  intro H3; apply H.
  apply* indom_write_inv.
  left.
  intro E; subst.
  apply H2; constructor.

  apply~ binds_write_neq.
  left; intro; subst.
  apply H2; constructor.

apply IHproto.
intro H3; apply H2; clear H2.
applys* in_protochain_next l'0.
Qed.

End ProtoChain.

Section Proto.

Lemma proto_trans :
  forall h f l l' x,
  in_protochain h f l l' ->
  proto h f l' x ->
  proto h f l x.
Proof.
introv IPC; induction~ IPC.
intro P.
applys* proto_next l'.
Qed.

Lemma proto_trans_middle :
  forall h f l l' x,
  ok_heap h ->
  in_protochain h f l l' ->
  proto h f l x ->
  proto h f l' x.
Proof.
introv OK IPC; induction~ IPC.
intro P; apply~ IHIPC.
inversion P; subst.
  forwards*: ok_heap_null H0.
  false~ H.
forwards*: binds_func_loc H0 H2.
subst~.
Qed.

Lemma proto_write (h : heap) nx ny lx ly l' vx :
  nx <> ny ->
  (field_proto <> nx \/ ~ in_protochain h ny ly lx) -> proto h ny ly l' ->
    proto (write h lx nx vx) ny ly l'.
Proof.
intros D nxpODl Hl'.
induction Hl'.
  constructor.

  apply proto_here.
  apply~ indom_write.

  applys* proto_next l'.
  generalize H.
  apply contrapose_intro.
  intro H1; applys indom_write_inv H1.
  right~.
  applys binds_write_neq H0.
  destruct nxpODl; [right~ | left~].
    intro; subst.
    apply H1; constructor.
  apply~ IHHl'.
  destruct nxpODl; [left~ | right~].
  intro H2; apply H1.
  apply* in_protochain_next.
Qed.

End Proto.

Section GeneralLemmas.

Lemma always_access_field_normal :
  forall h L e h' r,
  red_expr h L e (out_expr_ter h' (ret_expr_ref r)) ->
  exists n l, r = Ref l (field_normal n).
Proof.
introv R.
sets_eq v E: (ret_expr_ref r).
(*
induction R; try discriminate;
  try (inversion E; subst; do 2 eexists; reflexivity); subst;
  apply~ IHR2.
*)
skip.
Qed.

Lemma never_access_field_proto :
  forall h L e h' v l,
  red_expr h L e (out_expr_ter h' v) ->
  v <> Ref l field_proto.
Proof.
introv H; intro_subst. forwards* (n & l' & E): always_access_field_normal. invert E.
Qed.

End GeneralLemmas.

Section Scopes.

Lemma scopes_ret_expr_has_proto :
  forall h f L l,
  ok_heap h ->
  (forall l : loc, In l L -> bound h l) ->
  scopes h f L l ->
  l <> loc_null ->
  exists l',
  proto h f l l' /\
  l' <> loc_null.
Proof.
introv OKH OKS S; induction S.
  intro D; false~ D.

  intro D.
  forwards*: proto_defined f l OKH.
  inversion H; subst; tryfalse.
  exists~ f.
  exists~ field_proto.
  rewrite* indom_equiv_binds.

  apply~ IHS.
  introv I; apply OKS.
  right~.
Qed.

Lemma scopes_unique :
  forall h f l l1 l2,
  ok_heap h ->
  scopes h f l l1 -> scopes h f l l2 ->
  l1 = l2.
Proof.
introv OK S; induction S; intro S2; inverts~ S2.
  false H0.
  applys~ proto_func H H5.
false H6.
applys~ proto_func H4 H.
Qed.

Lemma scopes_defined :
  forall h s L, ok_heap h ->
  (forall l, In l L -> bound h l) ->  (* TODO: Use ok_scope instead of this property,
                                                          once it will force loc_global to be in the scope chain. *)
  exists l, scopes h s L l.
Proof.
introv WF IDH.
induction L as [_ | l].
exists loc_null; constructor.
forwards* (l' & P): proto_defined.
 apply IDH.
 simpl; auto.
 tests: (l' = loc_null).
  destruct IHL as [l''].
  introv I; apply IDH; simpl.
   right~.
  subst; exists l''.
   apply* scopes_next.
 exists l.
  apply* scopes_here.
Qed.

Lemma scopes_write :
  forall h nx ny L lx ly vx,
  (forall l, In l L -> bound h l) ->
  nx <> ny -> (field_proto <> nx \/ forall l, In l L -> ~ in_protochain h ny l lx) ->
  scopes h ny L ly ->
  scopes (write h lx nx vx) ny L ly.
Proof.
introv DefLoc D Dfield sy.
induction sy.
  constructor.

  applys scopes_here l'.
  apply~ proto_write.
  destruct~ Dfield; right.
  apply H1; constructor~.
  auto.

  apply scopes_next.
  apply~ proto_write.
  destruct~ Dfield; right.
  apply H0; constructor~.
  apply~ IHsy.

  introv H'; apply DefLoc.
  unfold In.
  right; apply H'.

  destruct Dfield; [left~ | right~].
  intros; apply H0.
  right~.
Qed.

Lemma write_bound h L l' x v : (* This is temporary, waiting for the modification of `ok_scope'. *)
  (forall l : loc, In l L -> bound h l) ->
  (forall l : loc, In l L -> bound (write h l' x v) l).
Proof.
introv OKS I.
lets (f & H): OKS l I.
exists f.
apply~ indom_write.
Qed.

Lemma scopes_update :
  forall h nx ny L lx ly vx,
  (forall l, In l L -> bound h l) ->
  nx <> ny ->
  (field_proto <> nx \/
    (lx <> loc_null /\ forall l, In l L -> ~ in_protochain h ny l lx)) -> (* Can be changed to a AllBefore, I guess. *)
  scopes h ny L ly ->
  scopes (update h lx nx vx) ny L ly.
Proof.
introv DefLoc D Dfield sy.
unfold update; case_if*;
subst; apply~ scopes_write;
(destruct Dfield; [left~ | right*];
destruct~ H).
Qed.

Lemma scopes_alloc_fun : (* Used in a tactic *)
  forall h ny L ly l' s n e l,
  (forall l, In l L -> bound h l) ->
  scopes h ny L ly ->
  (ny <> field_body /\ ny <> field_proto /\ ny <> field_scope /\ ny <> field_normal_prototype) ->
  (forall l0, In l0 L -> ~ in_protochain h ny l0 l') ->
  scopes (alloc_fun h l' s n e l) ny L ly.
Proof.
introv DefLoc sy [nynb [nynp [nyns nynup]]] nbc.
repeat (apply~ scopes_write;
  repeat apply~ write_bound;
  try (left; discriminate)).
Qed.

Lemma scopes_alloc_obj : (* Used in a tactic *)
  forall h ny L ly l l',
  (forall l, In l L -> bound h l) ->
  scopes h ny L ly -> ny <> field_proto ->
  (forall l0, In l0 L -> ~ in_protochain h ny l0 l) ->
  scopes (alloc_obj h l l') ny L ly.
Proof.
introv DefLoc sy nyp nbc.
unfold alloc_obj.
apply~ scopes_write.
Qed.

Lemma in_protochain_constr :
  forall (h : heap) (l : loc) (f : field) (l' l'' : loc),
  ~ indom h l' f ->
  binds h l' field_proto (value_loc l'') ->
  in_protochain h f l l' ->
  in_protochain h f l l''.
Proof.
introv NI B IPC; induction IPC.
  applys* in_protochain_next l''.
  constructor.
applys* in_protochain_next l'.
Qed.

Lemma proto_write_change :
  forall h f l l'' v,
  ok_heap h ->
  l'' <> loc_null ->
  in_protochain h f l l'' ->
  proto (write h l'' f v) f l l''.
Proof.
introv OK D IPC.
induction IPC.
  apply~ proto_here.
  apply~ indom_write_eq.
tests: (l = l'').
  tests: (l'' = l'); subst.
    forwards*: non_direct_cyclic_proto h l'; false*.
    forwards*: non_cyclic_proto h l'' l' f.
    apply* in_protochain_constr.
    constructor.
applys* proto_next l'.
intro I; apply H.
apply~ (indom_write_inv I).

apply~ binds_write_neq.
Qed.

Lemma scopes_update_self :
  forall L l' h f v,
  l' <> loc_null ->
  ok_heap h ->
  (forall l : loc, In l L -> bound h l) ->
  scopes h f L l' -> scopes (update h l' f v) f L l'.
Proof.
introv D WF B S.
unfold update. case_if~.
assert (AllBefore (fun l => ~in_protochain (write h l' f v) f l l') l' L) as H.
  induction L.
    inversion S; subst; destruct~ D.
    inversion S; subst.
    constructor.
  constructor.
    intro D'; subst.
    apply scopes_ret_expr_has_proto in S; auto.
    lets* (l'0 & H1 & H2): S.
      apply H2; apply* proto_func.
  apply~ IHL.
  introv I; apply B.
  right~.
  intro H.
  assert (scopes h f (a :: L) a) as Sa.
    assert (exists x, proto h f l' x /\ x <> loc_null) as [x [H1 H2]].
      applys* scopes_ret_expr_has_proto L.
      introv I; apply B.
      right~.
    applys* scopes_here x.
    forwards* IPC : in_protochain_write_end.
    applys* proto_trans l'.
  assert (a = l'); [idtac | subst].
    applys* scopes_unique h f (a :: L).
  forwards*: scopes_ret_expr_has_proto h f L l'.
  introv I; apply B; right~.
  lets (Pr & D'): H0.
  apply D'.
  applys* proto_func. induction S.
  constructor.
applys* scopes_here l.
apply~ proto_here.
apply~ indom_write_eq.

tests: (l = l'); subst.
  applys scopes_here l'.
  constructor.
  apply~ indom_write_eq.
  apply D.

apply scopes_next.
assert (~in_protochain (write h l' f v) f l l') as NIPC.
  inversion H; subst~.

apply~ not_in_protochain_conserve_proto.
intro IPC; apply NIPC.
apply~ in_protochain_write_end_inv.

apply~ IHS.
  introv I; apply B.
  right~.

applys @AllBefore_destr l.
intro D'; subst; false.
eauto.
Qed.

Lemma scopes_update_changed h :
  ok_heap h ->
  forall f L l l' v,
  (forall l, In l L -> bound h l) ->
  l' <> loc_null ->
  scopes h f L l ->
  in_protochain h f l l' ->
  scopes (update h l' f v) f L l.
Proof.
introv WF B D S ipc.

assert (l <> loc_null) as Dl.
  intro; subst.
  assert (l' = loc_null) as El'.
    applys* in_protochain_null_eq_null h f.
  apply~ D.

assert (AllBefore (fun l => proto h f l loc_null /\ ~in_protochain h f l l') l L) as AB.
  induction L.
    assert (scopes h f nil loc_null) as S0.
      constructor.
    assert (l = loc_null) as El.
      applys* scopes_unique h f (@nil loc).
    false~ Dl.
  tests: (a = l).
    subst; constructor.
  constructor~.
    apply~ IHL.
    introv I; apply B; right~.
    inversion S; subst~.
    false.
  split.

  inversion S; subst~.
    false.

  intro IPC.
  assert (scopes h f (a :: L) a) as Sa.
    forwards* (r & ? & ?): scopes_ret_expr_has_proto h f (a :: L) l.
    assert (proto h f a r) as P.
      applys~ proto_trans l'.
      applys~ proto_trans_middle l.
    apply* scopes_here.
  forwards* : scopes_unique Sa S.

induction AB.
  applys~ scopes_here l'.
  unfold update; case_if*.
  apply~ proto_write_change.
apply~ scopes_next.
  lets (P & NIP): H0.
  unfold update. cases_if*.
  apply~ not_in_protochain_conserve_proto.
apply~ IHAB.
  introv I; apply~ B.
  right~.
inversion S; subst~.
false~ H.
Qed.

End Scopes.

Section Fresh.

Lemma fresh_not_in_protochain h :
  ok_heap h ->
  forall x l f,
  fresh h x ->
  bound h l ->
  ~ in_protochain h f l x.
Proof.
introv WF (H & H0) B.
intro H1; apply H0; clear H0.
induction~ H1.
apply* IHin_protochain.
inverts keep WF.
unfold ok_heap_ok_value_def in * |- .
forwards*: ok_heap_ok_value H1.
inverts H3.
 inverts H4.
 false H. apply* in_protochain_null_eq_null.
exists* field_proto.
Qed.

End Fresh.

Section LemmaForTactics.

(* The following lemmas are temporary, waiting for the addition of `Mem loc_global s' in ok_scope. *)
Lemma update_bound h L l' x v :
  (forall l : loc, In l L -> bound h l) ->
  (forall l : loc, In l L -> bound (update h l' x v) l).
Proof.
apply~ write_bound.
Qed.

Lemma alloc_fun_bound h L l' s n e l'' : (* Used in a tactic *)
  (forall l : loc, In l L -> bound h l) ->
  (forall l : loc, In l L -> bound (alloc_fun h l' s n e l'') l).
Proof.
introv OKS I.
lets (f & H): OKS l I.
unfold alloc_fun.
exists f.
apply~ indom_write_fields.
Qed.

Lemma alloc_obj_bound h L l' l'' : (* Used in a tactic *)
  (forall l : loc, In l L -> bound h l) ->
  (forall l : loc, In l L -> bound (alloc_obj h l' l'') l).
Proof.
introv OKS I.
lets (f & H): OKS l I.
unfold alloc_obj.
exists f.
apply~ indom_write.
Qed.

End LemmaForTactics.


(* broken since the change of syntax.

Section Defining_expressions.

Definition expr_var_assign s e :=
  expr_var_decl s (Some e).
Definition assign_variable x e :=
  expr_assign (expr_variable x) None e.
Definition expr_undefined := expr_skip. (* NEWSYNTAX: use skip instead of value_undef *)
Definition expr_bool b := expr_literal (literal_bool b).
Definition expr_number n := expr_literal (literal_number n).
Definition expr_string s := expr_literal (literal_string s).
Definition expr_null := expr_literal literal_null.

Definition seq l :=
  match fold_right
      (fun e s =>
        match s with
        | None => Some e
        | Some e' => Some (expr_seq e e')
        end)
      None l
  with
  | None => expr_undefined
  | Some a => a
  end.

End Defining_expressions.

Section ProgramProperties.

Definition terminates prog :=
  forall h L,
    ok_heap h ->
    (forall l, In l L -> bound h l) ->
      exists h' v,
        red h L prog h' v.

End ProgramProperties.

Section Example.

Ltac reduce_seq :=
  repeat (try unfold seq; simpl; eapply red_seq).
Ltac unfold_defined :=
  try unfold assign_variable;
  try unfold expr_undefined;
  try unfold expr_bool;
  try unfold expr_number;
  try unfold expr_string;
  try unfold expr_null.

Ltac extractloc h L n x :=
  let l := fresh "l" x in
  let H := fresh "H" x in
  destruct (@scopes_defined h n%string L) as [l H]; auto.

Ltac solve_expr_literal :=
  econstructor; auto; apply getvalue_value.
Ltac solve_simpl_assign :=
  eapply red_assign;
  [ econstructor; try eauto
  | idtac
  | idtac
  | reflexivity
  ].

Ltac deals_with_bounds :=
  repeat (try apply update_bound;
  try apply alloc_fun_bound;
  try apply alloc_obj_bound).

Ltac reduce_scopes :=
  (repeat (
    match goal with
    | |- scopes (update _ _ _ _) _ _ _ => apply~ scopes_update; try (left~; discriminate; fail)
    | |- scopes (alloc_fun _ _ _ _ _ _) _ _ _ => apply~ scopes_alloc_fun; try (repeat split; discriminate)
    | |- scopes (alloc_obj _ _ _) _ _ _ => apply~ scopes_alloc_obj
    end
  ));
  try (deals_with_bounds; auto);
  try discriminate.

(* /* Here is the program we would like to prove. */
var x = null, y = null, z = null;
f = function(w){x = v; v = '4'; var v; y = v;};
v = '5'; f(null); z = v
*)

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.


Definition prog :=
  seq [
    expr_var_assign "x" expr_null;
    expr_var_assign "y" expr_null;
    expr_var_assign "z" expr_null;
    expr_var_assign "f" (expr_function None ["w"%string] (
      seq [
        expr_var_assign "v" expr_undefined;
        assign_variable "x" (expr_variable "v");
        assign_variable "v" (expr_string "4");
        assign_variable "y" (expr_variable "v")
      ]
    ));
    assign_variable "v" (expr_string "4");
    expr_call (expr_variable "f") [expr_null];
    assign_variable "z" (expr_variable "v")
  ].


Property prog_terminates :
  terminates prog.
Proof.
introv WF DefLoc.
eexists.
exists value_undef.  (* Here we know the ret_expr of the program, but that may
  not be the case:  an eexists should works. *)

unfold prog.

(* Defining locations and fresh variables. *)
extractloc h L "x"%string x.
extractloc h L "y"%string y.
extractloc h L "z"%string z.
extractloc h L "v"%string v.
extractloc h L "f"%string f.
do 2 edestruct fresh_exists.
 (* FIXME:  I need to prove that lx, ly, etc. are not loc_null, but for that I have
  to suppose that loc_global is in L.  I think it is always the case anyway. *)

reduce_seq; repeat (unfold_defined; simpl).

(* var *)
econstructor.
(* variable assignement *)
solve_simpl_assign.
(* value *)
solve_expr_literal.
(* getvalue *)
apply getvalue_value.

(* The same for `y'. *)
econstructor.
solve_simpl_assign.
reduce_scopes.
eexact Hy.
(* value *)
solve_expr_literal.
(* getvalue *)
apply getvalue_value.

(* The same for `z'. *)
econstructor.
solve_simpl_assign.
(* Some administration... *)
reduce_scopes.
eexact Hz.
(* value *)
solve_expr_literal.
(* getvalue *)
apply getvalue_value.

(* The same for `f'. *)
econstructor.
solve_simpl_assign.
reduce_scopes.
eexact Hf.
(* function unnamed *)
applys* red_function_unnamed @eq_refl @eq_refl.
(* getvalue *)
apply getvalue_value.

(* And for `v'. *)
solve_simpl_assign.
reduce_scopes.
eexact Hv.

(* Some administration. *)
intros; apply~ fresh_not_in_protochain.
(* (* NEWSYNTAX: No longer works *)
repeat apply~ ok_heap_update. (* This lemma has been removed: `ok_heap_write_user' should be used instead. *)
repeat apply~ update_bound.
eexact DefLoc.
auto.
intros; apply~ fresh_not_in_protochain.
repeat apply~ ok_heap_alloc_obj.
repeat apply~ ok_heap_update.
repeat apply~ alloc_obj_bound.
2: eexact H1.
intros; repeat apply~ update_bound.
2: eexact H2.
auto.

(* Valueue "4" *)
solve_expr_literal.
(* getvalue *)
apply getvalue_value.

(* call *)
eapply red_call; auto.
(* Variable `f' *)
econstructor.
(* reduce_scopes. *) (* Does not work. *)
apply~ scopes_update.
apply update_bound.
apply alloc_fun_bound.
apply alloc_obj_bound.
apply update_bound.
apply update_bound.
apply update_bound.
auto.
apply~ scopes_update_changed. (* Here is the faulty application of the automated tactic. *)
apply ok_heap_alloc_fun.
apply ok_heap_alloc_obj.
repeat apply~ ok_heap_update.
apply alloc_fun_bound.
apply alloc_obj_bound.
repeat apply~ update_bound.

skip. (* FIXME: needs the fact that loc_global is in the heap. *)

reduce_scopes.
eexact Hf.
intros; apply~ fresh_not_in_protochain.
repeat apply~ ok_heap_update.
repeat apply~ update_bound.
eexact DefLoc.
auto.
intros; apply~ fresh_not_in_protochain.
apply ok_heap_alloc_obj.
repeat apply~ ok_heap_update.
apply~ alloc_obj_bound.
intros; repeat apply~ update_bound.
eexact DefLoc.
eexact H2.
auto.
constructor.

econstructor.
apply~ proto_here.
skip (* FIXME: Need internal representation of a heap. *).

skip. (* FIXME: needs the fact that loc_global is in the heap. *)
skip. (* Idem. *)
Existential 4 := lf. skip (* idem *).
skip (* idem *).

(* TODO : *)
skip. skip. skip. skip. skip. skip. skip.
Existential 1 := h. Existential 1 := h. Existential 1 := value_loc loc_null. Existential 1 := loc_null.
Existential 1 := []. Existential 1 := ""%string.
Existential 1 := expr_variable "". Existential 1 := ret_expr_value (value_loc loc_null).
Existential 1 := ret_expr_value (value_loc loc_null).

Qed.*)
Admitted.

End Example.

*)
