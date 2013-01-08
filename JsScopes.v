Set Implicit Arguments.
Require Import Shared JsSemanticsAux JsWf JsWfAux.


(**************************************************************)

(** A few auxiliary results about scopes, for the intepreter *)

Section Proto.
Hint Constructors proto.

Lemma protochain_proto : forall h s l,
  protochain h l ->
  ok_heap h -> 
  exists l', proto h s l l'.
Proof.
  introv P O. induction P.
  exists~ loc_null.
  tests C: (indom h l s).
    exists~ l.
    forwards (l''&IH''): IHP. exists* l''.
Qed.

Lemma proto_defined : forall h s l, 
  bound h l ->
  ok_heap h ->
  exists l', proto h s l l'.
Proof.
  introv [f I] O. applys~ protochain_proto.
  applys* ok_heap_protochain_indom.
Qed.

Lemma proto_func : forall h f l l1 l2,
  proto h f l l1 -> 
  proto h f l l2 ->
  ok_heap h ->
  l1 = l2.
Proof.
  introv P1. induction P1; introv P2 O; inverts P2. 
  auto.
  auto.
  false* ok_heap_null.
  auto.
  auto.
  false.
  false* ok_heap_null.
  false.
  forwards*: binds_func_loc H0 H2. subst*.
Qed.

End Proto.

Section ScopeBound.
Hint Constructors Forall.

Lemma ok_scope_all_bound : forall h s,
  ok_scope h s ->
  ok_heap h ->
  Forall (bound h) s.
Proof.
  introv S O. induction S.
  constructors*. forwards S: (ok_heap_special O).
   forwards*: (ok_heap_special_global_this S). apply* binds_bound.
  constructors*. applys* indom_bound.
Qed.

End ScopeBound.
