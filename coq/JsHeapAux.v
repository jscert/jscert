Require Import JsSemantics.
Require Import LibOperation.

Definition inverse_worker {A B} (f : A -> B) (f' : B -> A) :=
  forall x, f'(f(x)) = x.

Inductive inverse {A B} (f : A -> B) (f' : B -> A) : Prop :=
  | inverse_intro : 
    inverse_worker f f' -> 
    inverse_worker f' f ->
    inverse f f'.

Section LocSubstitution.

Definition loc_normal_subst := nat -> nat.

(* Substitution of normal locations *)
Variable f : loc_normal_subst.
Variable f_inj : injective f.

Definition loc_subst (l : loc) : loc :=
  match l with
    | loc_normal n => loc_normal (f n)
    | _ => l
  end.

Lemma injective_loc_subst : injective loc_subst.
Proof.
  intros x y e.
  destruct x; destruct y; simpl in *; inversion e; trivial.
  rewrite (f_inj _ _ H0).
  trivial.
Qed.

Definition scope_subst (s : scope) : scope :=
  List.map loc_subst s.

Definition value_subst (v : value) : value :=
  match v with
   | value_loc l => value_loc (loc_subst l)
   | value_scope s => value_scope (scope_subst s)
   | _ => v
  end.

End LocSubstitution.

Inductive heap_subst (f : loc_normal_subst) (H H' : heap) : Prop :=
  | heap_subst_intro : (forall l x v, 
    binds H l x v ->
    binds H' (loc_subst f l) x (value_subst f v)) ->
    heap_subst f H H'.

Inductive heap_related 
  (f f' : loc_normal_subst) 
  (H H' : heap) : Prop :=
  | heap_related_intro : 
    inverse f f' ->
    heap_subst f H H' -> heap_subst f' H' H -> heap_related f f' H H'.

Section HeapSubstLemmas.

Variable f : loc_normal_subst.
Variable h h' : heap.
Variable P : heap_subst f h h'.

Lemma subst_indom : forall l x, indom h l x -> indom h' (loc_subst f l) x.
Proof.
  intros.
  unfold indom in *.
  rewrite Heap.indom_equiv_binds.
  rewrite Heap.indom_equiv_binds in H.
  destruct H.
  exists (value_subst f x0).
  destruct P.
  apply* H0.
Qed.

Lemma subst_read : forall l x, indom h l x ->
  read h' (loc_subst f l) x = value_subst f (read h l x).
Proof.
  intros.
  unfold read.
  rewrite <- Heap.binds_equiv_read.
  assert (exists v, Heap.read h (Ref l x) = v).
    exists (Heap.read h (Ref l x)); trivial.
  destruct H0 as [v A].
  rewrite A.
  rewrite <- Heap.binds_equiv_read in A; trivial.
  apply P; trivial.
  apply subst_indom; trivial.
Qed.

Lemma subst_bound : forall l, bound h l -> bound h' (loc_subst f l).
Proof.
  intros.
  destruct H.
  exists x.
  apply subst_indom.
  trivial.
Qed.

Lemma subst_write : 
  injective f ->
  forall l x v, heap_subst f 
    (write h l x v) 
    (write h' (loc_subst f l) x (value_subst f v)).
Proof.
  intros.
  split.
  intros.
  assert (A := Heap.binds_write_inv H0).
  destruct A as [A|A].
  destruct A as [A B].
  subst v.
  inversion A.
  subst l0. subst x0.
  apply Heap.binds_write_eq.
  apply Heap.binds_write_neq.
  apply P.
  destruct A. trivial.
  destruct A.
  intros A. apply H1.
  inversion A.
  rewrite (injective_loc_subst _ H _  _ H4).
  trivial.
Qed.

Lemma subst_rem : 
  injective f ->
  forall l x, heap_subst f
    (rem h l x)
    (rem h' (loc_subst f l) x).
Proof.
  intros.
  split.
  intros.
  assert (A := Heap.binds_rem_inv H0).
  destruct A as [A B].
  apply Heap.binds_rem.
  apply P; trivial.
  intros C; apply A.
  inversion C.
  rewrite (injective_loc_subst _ H _ _ H2).
  trivial.
Qed.

Lemma subst_empty : heap_subst f empty_heap empty_heap.
Proof.
  split.
  intros l x v A.
  assert (indom empty_heap l x).
    unfold indom. rewrite Heap.indom_equiv_binds.
    exists v; trivial.
  unfold indom in H.
  unfold Heap.indom in H.
  unfold empty_heap in H.
  rewrite Heap.dom_empty in H.
  destruct (set_in_empty_inv H).
Qed.

End HeapSubstLemmas.

Section HeapRelatedLemmas.

Variable f f' : loc_normal_subst.
Variable h h' : heap.
Variable P : heap_related f f' h h'.

Lemma related_indom1 : forall l x, indom h l x -> indom h' (loc_subst f l) x.
Proof.
  destruct P.
  apply* subst_indom.
Qed.

Lemma related_indom2 : forall l x, indom h' l x -> indom h (loc_subst f' l) x.
Proof.
  destruct P.
  apply* subst_indom.
Qed.

Lemma related_bound : forall l, bound h l -> bound h' (loc_subst f l).
Proof.
  destruct P.
  apply* subst_bound.
Qed.

Lemma related_read1 : forall l x, indom h l x ->
  read h' (loc_subst f l) x = value_subst f (read h l x).
Proof.
  destruct P.
  apply* subst_read.
Qed.

Lemma related_read2 : forall l x, indom h' l x ->
  read h (loc_subst f' l) x = value_subst f' (read h' l x).
Proof.
  destruct P.
  apply* subst_read.
Qed.

End HeapRelatedLemmas. 

