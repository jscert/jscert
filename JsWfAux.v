Set Implicit Arguments.
Require Import JsSemanticsAux JsWf.
Implicit Types h : heap.


(**************************************************************)
(** ** More tactics *)

Hint Constructors ok_value ok_ret_expr ok_scope basic_value.

Ltac protochain_step :=
  eapply protochain_step; [ binds_simpl |  ].

Ltac protochain_end :=
  eapply protochain_end.


(**************************************************************)
(** ** Lemmas about [extends_proto] *)

Lemma extends_proto_elim : forall h h' l,
  extends_proto h h' -> has_some_proto h l -> has_some_proto h' l.
Proof. auto*. Qed.

(** [extends_proto] is a reflexive and transitive relation *)

Lemma extends_proto_refl : refl extends_proto.
Proof. intros x. unfolds extends_proto. eauto. Qed.

Lemma extends_proto_trans : trans extends_proto.
Proof. introv H1 H2. unfolds extends_proto. eauto. Qed.

Hint Resolve extends_proto_refl.


(**************************************************************)
(** ** Initial heap *)

Lemma init_heap_wf : ok_heap init_heap.
Proof.
  constructors.  
    introv H. binds_cases H.
      protochain_step. protochain_end. 
      protochain_step. protochain_end.
      protochain_step. protochain_step. protochain_end.
      protochain_step. protochain_end.
      protochain_step. protochain_step. protochain_end.
    introv B N. binds_cases* B; apply ok_value_loc; indom_simpl.    
    introv H. exists loc_global. binds_cases H. splits. 
      auto.
      binds_simpl.
      indom_simpl.
    introv [H|H]; binds_cases H. 
    introv H. binds_cases H.
    constructors; try (indom_simpl). binds_simpl.
Qed.

Lemma init_scope_ok : ok_scope init_heap init_scope.
Proof.
  unfold init_scope.
  repeat constructor.
  forwards~ OS: ok_heap_special init_heap_wf.
  forwards~: ok_heap_special_global_proto OS.
Qed.

(**************************************************************)
(** ** Auxiliary results about well-formedness *)

(** For every bound pair [(l,f)], [l] has a prototype chain
    --same as [ok_heap_proto_def] but using [indom] instead of [bound] *)

Lemma ok_heap_protochain_def_indom : forall h l f,
  indom h l f -> 
  ok_heap_protochain_def h -> 
  protochain h l.
Proof. introv I O. lets (?&?): indom_binds I. apply* O. Qed.

Lemma ok_heap_protochain_indom : forall h l f,
  indom h l f ->
  ok_heap h ->
  protochain h l.
Proof.
  introv I O. lets: ok_heap_protochain O. applys* ok_heap_protochain_def_indom.
Qed.

Lemma ok_heap_protochain_bound : forall h l,
  bound h l ->
  ok_heap h ->
  protochain h l.
Proof. introv (f&I) O. apply* ok_heap_protochain_indom. Qed.

(** If a non-null location has a [protochain] then 
    it [has_some_proto] *)

Lemma protochain_has_some_proto : forall h l,
  protochain h l -> 
  l <> loc_null -> 
  has_some_proto h l.
Proof. introv H N. inverts H. false. apply* binds_indom. Qed.

(** Preserving prototype fields ensures preservation of scopes *)

Lemma ok_scope_extends : forall h1 h2 s,
  ok_scope h1 s ->
  extends_proto h1 h2 -> 
  ok_scope h2 s.
Proof. introv O E. induction O; constructors*. Qed.

(** [value_scope] can only be found at a [field_scope] *)

Lemma ok_heap_scope : forall h l f s,
  ok_heap h ->
  binds h l f (value_scope s) -> 
  f = field_scope. 
Proof. 
  introv O B. tests C: (not_scope_or_body f).
    forwards* OV: ok_heap_ok_value C. inverts OV as M. inverts* M.
    unfolds not_scope_or_body. rew_logic in C. destruct* C.
     subst. forwards* (s'&x'&e'&v'&_&Bb&_&_): ok_heap_function O.
     false (binds_func Bb B).
Qed.

(** [value_body] can only be found at a [field_body] *)

Lemma ok_heap_body : forall h l f x e,
  ok_heap h ->
  binds h l f (value_body x e) -> 
  f = field_body.
Proof. 
  introv O B. tests C: (not_scope_or_body f).
    forwards* OV: ok_heap_ok_value C. inverts OV as M. inverts* M.
    unfolds not_scope_or_body. rew_logic in C. destruct* C.
     subst. forwards* (s'&x'&e'&v'&Bs&_&_&_): ok_heap_function O.
     false (binds_func Bs B).
Qed.

(** [field_scope] can only be mapped to a [value_scope].
    (Note: never used in proofs) *)

Lemma ok_heap_scope_inv : forall h l v,
  ok_heap h ->
  binds h l field_scope v -> 
  exists s, v = value_scope s.
Proof.
  introv O B. forwards* (s&x&e&v'&Bs&_&_&_): ok_heap_function O. 
  exists s. applys binds_func B Bs.
Qed.

(** [field_body] can only be bound to a [value_body].
    (Note: never used in proofs)  *)

Lemma ok_heap_body_inv : forall h l v ,
  ok_heap h ->
  binds h l field_body v -> 
  exists x e, v = value_body x e.
Proof.
  introv O B. forwards* (s&x&e&v'&_&Bb&_&_): ok_heap_function O. 
  exists x e. applys binds_func B Bb.
Qed.

(** Non-null locations found in the store at regular fields 
    correspond to objects that have a prototype *)

Lemma ok_heap_binds_loc_has_proto : forall h l l' f, 
  ok_heap h ->
  binds h l f (value_loc l') -> 
  f <> field_body ->
  f <> field_scope ->
  l' <> loc_null -> 
  has_some_proto h l'.
Proof.
  introv O B H1 H2 N. forwards~ M: ok_heap_ok_value B.
  inverts M as M. inverts* M. auto.
Qed.

(** Scopes stored in a well-formed heap are well-formed *)

Lemma ok_heap_binds_ok_scope : forall h l n s, 
  ok_heap h -> 
  binds h l n (value_scope s) -> 
  ok_scope h s.
Proof.
  introv O B. forwards* E: ok_heap_scope B. subst.
  forwards* (s'&x'&e'&v'&Bs&_&_&Os): ok_heap_function O. 
  lets E: (binds_func B Bs). inverts* E.
Qed.

(** The null location is not allocated in a well-formed heap *)

Lemma ok_heap_null_indom : forall h f,
  ok_heap h -> indom h loc_null f -> False.
Proof.
  introv O I. forwards (v&B): indom_binds I. 
  applys* ok_heap_null.
Qed.


(**************************************************************)
(** * Other lemmas that apply in well-formed heaps *)

(** The ret_expr of scope resolution, if it not null,
    is a location for which the prototype resolution
    returns a non-null object *)

Lemma scopes_proto_not_null : forall h s f l,
  scopes h f s l ->
  ok_heap h ->
  l <> loc_null ->
  exists l', l' <> loc_null /\ proto h f l l'.
Proof. introv S O D. induction* S. Qed.

(** If prototype resolution succeeds for [(f,l)],
    with [l] not null, then [l] has a prototype field *)
 
Lemma proto_has_some_proto : forall h l l' f,
  proto h f l l' ->
  ok_heap h ->
  l <> loc_null ->
  has_some_proto h l.
 Proof.
  introv P O N. inverts P as.
  false*.
  introv H. lets(v&B): indom_binds H.
   forwards~ M: ok_heap_protochain B.
   forwards~: protochain_has_some_proto M.
  introv I B P.
   forwards~ M: ok_heap_protochain B.
   forwards~: protochain_has_some_proto M.
 Qed.

(** If the ret_expr of prototype resolution for [(f,l)] returns a
    non-null location [l'], then [(l',f)] is bound in the heap. *)

Lemma proto_indom : forall h l f l',
  proto h f l l' ->
  ok_heap h ->
  l' <> loc_null ->
  indom h l' f.
Proof. introv P O N. induction* P. Qed.

