Set Implicit Arguments.
Require Import JsSemanticsAux JsWf JsWfAux.
Implicit Type h : heap.


(**************************************************************)
(** ** Tactics *)

Hint Extern 1 (_ <> _ :> (loc*field)%type) => congruence.
Hint Extern 1 (_ <> _ :> field) => congruence.
Hint Extern 1 (field_normal_prototype <> _) => unfold field_normal_prototype.
Hint Extern 1 (_ <> field_normal_prototype) => unfold field_normal_prototype.


(**************************************************************)
(** ** Preservation of [has_some_proto] *)

Lemma has_some_proto_write : forall h l' l f v,
  has_some_proto h l' ->
  has_some_proto (write h l f v) l'.
Proof. introv H. indom_simpl~. Qed.

Lemma has_some_proto_write_fields : forall h l' l fvs,
  has_some_proto h l' ->
  has_some_proto (write_fields h l fvs) l'.
Proof. lets: has_some_proto_write. intros. apply* write_fields_ind. Qed.

Lemma has_some_proto_rem : forall h l' l f,
  has_some_proto h l' ->
  f <> field_proto ->
  has_some_proto (rem h l f) l'.
Proof. introv H N. apply* indom_rem. Qed.

Lemma has_some_proto_write_proto : forall h l l',
  has_some_proto (write_proto h l l') l.
Proof. introv. indom_simpl~. Qed.

Lemma has_some_proto_not_null : forall h l,
  ok_heap h ->
  has_some_proto h l ->
  l <> loc_null.
Proof.
  introv O P E. subst. lets (v&B): indom_binds P.
   apply* ok_heap_null.
Qed.

Hint Resolve has_some_proto_write has_some_proto_rem.


(**************************************************************)
(** ** Preservation of [has_null_proto] *)

Lemma has_null_proto_write : forall h l' l f v,
  has_null_proto h l' ->
  f <> field_proto ->
  has_null_proto (write h l f v) l'.
Proof. introv H N. apply* binds_write_neq. Qed.

Lemma has_null_proto_rem : forall h l' l f,
  has_null_proto h l' ->
  f <> field_proto ->
  has_null_proto (rem h l f) l'.
Proof. introv H N. apply* binds_rem. Qed.

Hint Resolve has_null_proto_write has_null_proto_rem.


(**************************************************************)
(** ** Preservation of [extends_proto] *)

Lemma extends_proto_write : forall h l f v,
  extends_proto h (write h l f v).
Proof. introv H. auto~. Qed.

Lemma extends_proto_write_fields : forall h l fvs,
  extends_proto h (write_fields h l fvs).
Proof.
  hint extends_proto_write, extends_proto_trans.
  intros. apply* write_fields_ind.
Qed.

Lemma extends_proto_rem : forall h l f,
  f <> field_proto ->
  extends_proto h (rem h l f).
Proof. introv N B. auto~. Qed.

Lemma extract_heap_from_output_expr_extends : forall h0 h o, (* Martin:  I guess this lemma can be simplified.  FIXME:  Is it even useful? *)
  (forall h' r, o = out_expr_ter h' r -> extends_proto h h') ->
  extends_proto h0 h ->
  extends_proto h0 (extract_heap_from_output_expr h o).
Proof.
  introv I E. destruct o.
    simpl. auto.
    simpl. applys* extends_proto_trans E.
Qed.

Hint Resolve extends_proto_write extends_proto_write_fields.


(**************************************************************)
(** ** Preservation of [ok_scope] *)

Lemma ok_scope_write : forall h l s f v,
  ok_scope h s ->
  ok_scope (write h l f v) s.
Proof. introv O. induction* O. Qed.

Lemma ok_scope_write_fields : forall h s l lfv,
  ok_scope h s ->
  ok_scope (write_fields h l lfv) s.
Proof.
introv O. apply~ write_fields_ind. introv O'.
apply* ok_scope_write.
Qed.

Lemma ok_scope_rem : forall h l f s,
  ok_scope h s ->
  f <> field_proto ->
  ok_scope (rem h l f) s.
Proof. introv O N. induction* O. Qed.


(**************************************************************)
(** ** Preservation of [ok_value] *)

Lemma ok_value_write : forall h l f v v',
  ok_value h v ->
  ok_value (write h l f v') v.
Proof.
  introv V. destruct V.
  apply~ ok_value_basic.
  apply~ ok_value_loc.
Qed.

Lemma ok_value_rem: forall h l f v,
  ok_value h v ->
  f <> field_proto ->
  ok_value (rem h l f) v.
Proof.
  introv V NP. destruct V.
  apply* ok_value_basic.
  apply* ok_value_loc.
Qed.

Lemma ok_value_extends : forall h h' v,
  ok_value h v ->
  extends_proto h h' ->
  ok_value h' v.
Proof. introv V E. inverts* V. Qed.


(**************************************************************)
(** ** Preservation of [protochain] *)

Lemma protochain_write_not_proto : forall h l l' f v,
  protochain h l' ->
  f <> field_proto ->
  protochain (write h l f v) l'.
Proof.
  introv C F. induction C.
  apply protochain_end.
  applys protochain_step l'. binds_simpl~. auto.
Qed.

Lemma protochain_write_proto : forall h h' l l' v,
  protochain h l' ->
  h' = write h l field_proto v ->
  protochain h' l ->
  protochain h' l'.
Proof.
  introv C E L. subst. induction C.
  apply protochain_end.
  tests: (l0 = l).
    auto.
    apply* protochain_step. binds_simpl*.
Qed.

Lemma protochain_add_proto : forall h l l' v,
  protochain h l ->
  fresh h l' ->
  protochain (write h l' field_proto v) l.
Proof.
  introv C F. induction C.
  constructors.
  constructors.
    binds_simpl.
      left. apply* fresh_binds_neq.
      eauto.
    eauto.
Qed.

Lemma protochain_new_proto : forall h l l',
  protochain h l ->
  fresh h l' ->
  protochain (write h l' field_proto l) l'.
Proof. introv P F. protochain_step. apply* protochain_add_proto. Qed.

Lemma protochain_rem : forall h l l' f,
  protochain h l ->
  f <> field_proto ->
  protochain (dealloc h (Ref l' f)) l.
Proof.
  introv C N. induction C.
  constructor.
  apply* protochain_step. apply* binds_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_special] *)

Lemma ok_heap_special_write : forall h l f v,
  ok_heap_special_def h ->
  l <> loc_null ->
  (l,f) <> (loc_scope,field_this) ->
  ok_heap_special_def (write h l f v).
Proof.
  introv [H1 H2 H3 H4] N1 N2. constructors.
  binds_simpl~. rewrite <- not_and. intros [E1 E2]. false.
  indom_simpl~.
  indom_simpl~.
  indom_simpl~.
Qed.

Lemma ok_heap_special_rem : forall h l x,
  ok_heap_special_def h ->
  ok_heap_special_def (rem h l (field_normal x)).
Proof.
  introv [H1 H2 H3 H4]. constructors.
  apply* binds_rem.
  apply* indom_rem.
  apply* indom_rem.
  apply* indom_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_protochain] *)

Section OkHeapProto.

Hint Resolve protochain_write_not_proto.

Lemma ok_heap_protochain_write_not_proto : forall h l f v,
  ok_heap_protochain_def h ->
  let h' := write h l f v in
  f <> field_proto ->
  protochain h' l ->
  ok_heap_protochain_def h'.
Proof. introv M N B R. binds_cases* R. Qed.

Lemma ok_heap_protochain_write_proto : forall h l v,
  ok_heap_protochain_def h ->
  let h' := write h l field_proto v in
  protochain h' l ->
  ok_heap_protochain_def h'.
Proof.
  introv B C R. binds_cases R.
  auto.
  apply* protochain_write_proto.
Qed.

Lemma ok_heap_protochain_rem : forall h l f,
  ok_heap_protochain_def h ->
  f <> field_proto ->
  ok_heap_protochain_def (rem h l f).
Proof.
  introv W N B.
  forwards [_ ?]: binds_rem_inv B. apply* protochain_rem.
Qed.

End OkHeapProto.


(**************************************************************)
(** ** Preservation of [ok_heap_loc] *)

Lemma ok_heap_ok_value_write : forall h l f v,
  ok_heap_ok_value_def h ->
  ok_value h v ->
  ok_heap_ok_value_def (write h l f v).
Proof.
  introv O V B N. destruct V.
    binds_cases* B. apply* ok_value_write.
    binds_cases* B. apply* ok_value_write.
Qed.

Lemma ok_heap_ok_value_write_scope_body : forall h l f v,
  ok_heap_ok_value_def h ->
  f = field_scope \/ f = field_body ->
  ok_heap_ok_value_def (write h l f v).
Proof.
  introv O V B N. unfolds in N. destruct V.
    binds_cases* B. apply* ok_value_write.
    binds_cases* B. apply* ok_value_write.
Qed.

Lemma ok_heap_ok_value_rem : forall h l x,
  ok_heap_ok_value_def h ->
  ok_heap_ok_value_def (dealloc h (Ref l (field_normal x))).
Proof.
  introv O B N. lets (B1&B2): binds_rem_inv B.
  apply* ok_value_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_this] *)

Lemma ok_heap_this_write_not_this : forall h l f v,
  ok_heap_this_def h ->
  f <> field_this ->
  (f = field_proto -> indom h l field_this -> v = value_loc loc_null) ->
  ok_heap_this_def (write h l f v).
Proof.
  introv O T P H. binds_cases H.
  lets (l'&F&N&HP): O H. exists l'. splits*.
  tests: (l0 = l /\ f = field_proto).
    inverts C. rewrite~ P. binds_simpl. apply* binds_indom.
    apply* binds_write_neq.
Qed.

Lemma ok_heap_this_write_this : forall h l l',
  ok_heap_this_def h ->
  has_null_proto h l ->
  has_some_proto h l' ->
  ok_heap_this_def (write h l field_this (value_loc l')).
Proof.
  introv O N P H. binds_cases H.
    exists* l'.
    lets (x&E&M&S): O H. exists* x.
Qed.

Lemma ok_heap_this_rem : forall h l x,
  ok_heap_this_def h ->
  ok_heap_this_def (rem h l (field_normal x)).
Proof.
  introv O B. lets (B1&B2): binds_rem_inv B.
  lets (y&E&N&S): O B2. exists* y.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_function] *)

Lemma ok_heap_function_write_not_fun : forall h l f v,
  ok_heap_function_def h ->
  not_scope_or_body f ->
  ok_value h v ->
  ok_heap_function_def (write h l f v).
Proof.
  introv O N NP B. unfolds in N.
  forwards (s&x&e&l'&Bs&Bb&Bu): O.
    destruct B as [B|B]; binds_cases* B.
  exists s x e (If (Ref l f = Ref l0 field_normal_prototype) then v else l').
  splits.
    apply* binds_write_neq.
    apply* binds_write_neq.
    case_if as C.
      inverts C. apply* binds_write_eq.
      apply* binds_write_neq. applys not_not_elim.
        intros M. rew_logic in M. false* C. inverts~ M. (* LATER: use tactic [down] *)
    apply* ok_scope_write.
Qed.

Lemma ok_heap_function_alloc_fun : forall h l l' s x e,
  ok_heap_function_def h ->
  ok_scope h s ->
  has_some_proto h l ->
  ok_heap_function_def (alloc_fun h l' s x e l).
Proof.
  introv O S P B. destruct B.
  (* case: binds field_scope *)
  binds_cases* H.
    exists s x e l. splits*.
      apply* binds_write_neq. apply* binds_write_eq.
      apply* binds_write_eq.
      do 2 apply* binds_write_neq. apply* binds_write_eq.
      do 4 apply* ok_scope_write.
    forwards* (x'&e'&l1&B&E&F): O l0 v. exists x' e' l1 B.
     splits*; try (do 4 apply* binds_write_neq).
       do 4 apply* ok_scope_write.
  (* case: binds field_body (copy-pasted, but hard to factorize) *)
  binds_cases* H.
    exists s x e l. splits*.
      apply* binds_write_neq. apply* binds_write_eq.
      apply* binds_write_eq.
      do 2 apply* binds_write_neq. apply* binds_write_eq.
       do 4 apply* ok_scope_write.
    forwards* (x'&e'&l1&B&E&F): O l0 v. exists x' e' l1 B.
     splits*; try (do 4 apply* binds_write_neq).
       do 4 apply* ok_scope_write.
Qed.

Lemma ok_heap_function_rem : forall h l x,
  ok_heap_function_def h ->
  x <> "prototype"%string ->
  ok_heap_function_def (rem h l (field_normal x)).
Proof.
  introv O P B. destruct* B as [B|B];
    binds_cases* B; lets(N&B'): binds_rem_inv B.
  (* case: binds field_scope *)
  forwards* (s'&x'&e'&v'&Bs&Bb&Bu): O. exists s' x' e' v'.
   splits*; try (apply* binds_rem). apply* ok_scope_rem.
  (* case: binds field_body (copy-pasted, but hard to factorize) *)
  forwards* (s'&x'&e'&v'&Bs&Bb&Bu): O. exists s' x' e' v'.
   splits*; try (apply* binds_rem). apply* ok_scope_rem.
Qed.


(**************************************************************)
(** ** Preservation of [ok_heap_null] *)

Lemma ok_heap_null_write : forall h l f v,
  ok_heap_null_def h ->
  l <> loc_null ->
  ok_heap_null_def (write h l f v).
Proof. introv O N. introv B. binds_cases* B. Qed.

Lemma ok_heap_null_rem : forall h l x,
  ok_heap_null_def h ->
  ok_heap_null_def (rem h l (field_normal x)).
Proof. introv O B. lets* [? ?]: (binds_rem_inv B). Qed.


(**************************************************************)
(** ** Lemmas about [ok_ret_expr] and [ok_value] *)

Lemma ok_ret_expr_loc : forall h l,
  has_some_proto h l ->
  ok_ret_expr h l.
Proof. introv H. apply ok_ret_expr_value. apply~ ok_value_loc. Qed.

Lemma ok_ret_expr_prove : forall h v r,
  ok_heap h ->
  ok_ret_expr h r ->
  getvalue h r v ->
  ok_ret_expr h v.
Proof.
  introv O R G. inverts R as R.
  inverts~ G.
  inverts G as.
  (* case: getvalue_value *)
  introv G1 G2 G3 G4. apply ok_ret_expr_value. destruct~ v.
    (* subcase: v = loc *)
    intros. tests: (l = loc_null).
      apply* ok_value_basic.
      apply ok_value_loc. applys* ok_heap_binds_loc_has_proto O.
    (* subcase: v = value_scope j *)
    false (ok_heap_scope O G4).
    (* subcase: v = value_body j *)
    false (ok_heap_body O G4).
  (* case: getvalue_undef *)
  intros. constructors. constructors. auto.
Qed.

Lemma ok_ret_expr_instanceof_red : forall h l v v',
  instanceof_red h l v v' ->
  ok_ret_expr h v'.
Proof.
  introv H. induction* H.
Qed.

Lemma ok_ret_expr_binary_op_red : forall op v1 v2 v3 h,
  ok_value h v1 -> ok_value h v2 ->
  binary_op_red op h v1 v2 v3 ->
  ok_ret_expr h v3.
Proof.
  introv Ov1 Ov2 H. induction* H.
  applys* ok_ret_expr_instanceof_red.
Qed.

Lemma ok_ret_expr_has_some_proto  : forall h l,
  ok_ret_expr h (value_loc l) ->
  l <> loc_null ->
  has_some_proto h l.
Proof.
  introv O N. inverts O as O. inverts O as O.
  inverts O; tryfalse.
  auto.
Qed.

Hint Resolve ok_ret_expr_prove ok_ret_expr_binary_op_red ok_ret_expr_has_some_proto.

Lemma binds_this_loc_ok_ret_expr : forall h l l',
  binds h l field_this (value_loc l') ->
  ok_heap h ->
  ok_ret_expr h l'.
Proof.
  introv B O. apply ok_ret_expr_value. tests: (l' = loc_null).
    apply* ok_value_basic.
    apply ok_value_loc. forwards*: (ok_heap_ok_value O).
Qed.

Lemma obj_of_value_ok_ret_expr : forall h l l' v,
  l = obj_of_value v l' ->
  ok_ret_expr h v ->
  has_some_proto h l' ->
  ok_ret_expr h l.
Proof.
  introv E V P.
  subst l. forwards [(l1&E)|?]: (value_loc_or_not v).
    subst. simpl. case_if*.
    rewrite* obj_of_value_not_loc.
Qed.

Lemma getvalue_ok_value : forall h r v,
  getvalue h r v ->
  ok_ret_expr h r ->
  ok_heap h ->
  ok_value h v.
Proof.
  introv G R O. inverts R as R.
  inverts~ G.
  destruct R.
    subst. inverts G; false.
    inverts G as M1 M2 M3 M4.
      destruct v; try solve [ apply~ ok_value_basic ].
        tests: (l = loc_null).
          apply~ ok_value_basic.
          apply ok_value_loc. forwards*: (ok_heap_ok_value O M4).
        forwards*: (ok_heap_ok_value O M4).
        forwards*: (ok_heap_ok_value O M4).
      apply~ ok_value_basic.
Qed.


(**************************************************************)
(** ** Lemmas about [ok_scope] *)

Lemma ok_scope_inv_nil : forall h l s,
  ok_scope h (l :: s) -> s <> nil -> ok_scope h s.
Proof. introv O N. inverts O. false. auto. Qed.

Lemma ok_scope_inv : forall h h' l s,
  ok_scope h (l :: s) -> ok_scope h' s -> ok_scope h s.
Proof. introv O O'. apply* ok_scope_inv_nil. inverts O'; congruence. Qed.

Hint Resolve ok_scope_inv.


(**************************************************************)
(** ** Invariant about extended expressions *)
(* Martin:  Should it be moved to JsWf? *)

Inductive ok_out_expr h0 : out_expr -> Prop :=
  | ok_out_expr_normal : forall h r,
      ok_heap h ->
      ok_ret_expr h r ->
      extends_proto h0 h ->
      ok_out_expr h0 (out_expr_ter h r)
  | ok_out_expr_throw : forall h v,
      ok_heap h ->
      ok_value h v ->
      extends_proto h0 h ->
      ok_out_expr h0 (out_expr_ter h (res_expr_throw v)).

Inductive ok_out_prog h0 : out_prog -> Prop :=
  | ok_out_prog_normal : forall h r,
      ok_heap h ->
      ok_ret_expr h r ->
      extends_proto h0 h ->
      ok_out_prog h0 (out_prog_ter h r)
  | ok_out_prog_break : forall h la,
      ok_heap h ->
      (* Martin:  do we really need a `ok_label' property? *)
      extends_proto h0 h ->
      ok_out_prog h0 (out_prog_ter h (res_prog_break la))
  | ok_out_prog_continue : forall h la,
      ok_heap h ->
      (* Martin:  same question. *)
      extends_proto h0 h ->
      ok_out_prog h0 (out_prog_ter h (res_prog_continue la))
  | ok_out_prog_return : forall h r,
      ok_heap h ->
      ok_ret_expr h r ->
      extends_proto h0 h ->
      ok_out_prog h0 (out_prog_ter h (res_prog_return r))
  | ok_out_prog_throw : forall h v,
      ok_heap h ->
      ok_value h v ->
      extends_proto h0 h ->
      ok_out_prog h0 (out_prog_ter h (res_prog_throw v)).

Inductive ok_body_or_primitive h0 : body_or_primitive -> Prop :=
  | ok_body_or_primitive_normal_body : forall s lx P,
      ok_scope h0 s ->
      ok_body_or_primitive h0 (normal_body s lx P)

  | ok_body_or_primitive_primitive : forall (pr : primitive),
      ok_body_or_primitive h0 pr.

(* Martin:  I'm not totally sure of the following invariants. *)
Definition ok_ext_expr := correct_ext_expr
  ok_out_expr ok_out_prog extends_proto
  ok_value ok_ret_expr
  has_some_proto ok_body_or_primitive
  (fun _ => True) (fun _ => True).

Definition ok_ext_stat := correct_ext_stat
  ok_out_expr ok_out_prog extends_proto
  ok_scope ok_value ok_ret_expr
  has_some_proto ok_body_or_primitive
  (fun _ => True) (fun _ => True).

Definition ok_ext_prog := correct_ext_prog
  ok_out_prog.


(**************************************************************)
(** ** preservation of extended expressions's invariants *)

Lemma ok_out_expr_extends : forall h1 h0 o,
  ok_out_expr h1 o ->
  extends_proto h0 h1 ->
  ok_out_expr h0 o.
Proof.
  introv OK Ext.
  inverts OK;
   constructors~; applys~ extends_proto_trans h1.
Qed.

Lemma ok_out_prog_extends : forall h0 h1 o,
  ok_out_prog h1 o ->
  extends_proto h0 h1 ->
  ok_out_prog h0 o.
Proof.
  introv OK Ext.
  inverts OK;
   constructors~; applys~ extends_proto_trans h1.
Qed.


(**************************************************************)
(** ** Lemmas for hard cases of the proof of safety *)

Section Safety.
Hint Resolve ok_heap_special ok_heap_protochain.

(** Lemma for proving safety of [red_variable] *)

Lemma ok_ret_expr_variable_lookup : forall h s (l:loc) (x:string),
  scopes h x s l ->
  ok_heap h ->
  ok_scope h s ->
  ok_ret_expr h (ret_expr_ref (Ref l (field_normal x))).
Proof.
  introv H W O. inductions H.
  (* case: scope_null *)
  inverts O.
  (* case: scopes_here *)
  constructors. right. inverts H.
    false.
    inverts O.
      apply* protochain_has_some_proto. apply* ok_heap_protochain_def_indom.
      auto.
    forwards*: binds_indom H2.
  (* case: scopes_next *)
  asserts [M|M]: (l' = loc_null \/ s <> nil).
    inverts H0; congruence_on_disjunction.
    apply* ok_ret_expr_ref.
    apply* IHscopes. apply* ok_scope_inv_nil.
Qed.

(** Lemma for proving safety of [red_literal] *)

Lemma ok_ret_expr_value_of_literal : forall h i,
  ok_ret_expr h (value_of_literal i).
Proof.
  intros. applys ok_ret_expr_value.
  destruct i; simple~.
Qed.

(** Lemma for proving safety of [red_new] *)

Lemma obj_or_glob_of_value_protochain : forall h1 h2 l1 l2 f v1,
  binds h1 l1 f v1 ->
  l2 = obj_or_glob_of_value v1 ->
  extends_proto h1 h2 ->
  ok_heap h1 ->
  ok_heap h2 ->
  not_scope_or_body f ->
  protochain h2 l2.
Proof.
  introv B L E O1 O2 N. subst l2.
  forwards~: ok_heap_protochain_indom loc_obj_proto O2.
  forwards [(l3&E1)|?]: (value_loc_or_not v1).
    subst v1. simpl. case_if*.
     forwards* V: ok_heap_ok_value B. inverts V as M.
       inverts* M.
       applys~ ok_heap_protochain_indom. applys E M.
    rewrite~ obj_or_glob_of_value_not_loc.
Qed.

Lemma ok_heap_alloc_obj : forall h l l',
  protochain h l ->
  (l = loc_null \/ has_some_proto h l) ->
  fresh h l' ->
  ok_heap h ->
  ok_heap (alloc_obj h l' l).
Proof.
  unfold alloc_obj, write_proto.
  introv C P F [O1 O2 O3 O4 O5 O6]. constructors.
  apply* ok_heap_protochain_write_proto. apply* protochain_new_proto.
  destruct P.
    subst l. apply* ok_heap_ok_value_write.
    apply* ok_heap_ok_value_write.
  apply* ok_heap_this_write_not_this.
   introv _ M. false* fresh_not_indom.
  apply* ok_heap_function_write_not_fun. destruct P.
    constructor. subst l.
    apply basic_null.
  apply* ok_value_loc.
  apply* ok_heap_null_write.
  apply* ok_heap_special_write.
Qed.

Lemma ok_heap_alloc_fun : forall h l' s x e l,
  ok_scope h s ->
  has_some_proto h l ->
  fresh h l' ->
  ok_heap h ->
  ok_heap (alloc_fun h l' s x e l).
Proof.
  introv S P F [OP OL OT OF ON OS]. constructors.
   lets FP: ok_heap_special_function_proto OS.
  hint protochain_write_not_proto.
   sets h': (write h l' field_proto loc_func_proto).
   asserts H': (protochain h' l').
     apply* protochain_new_proto.
      lets (v&B): indom_binds FP. forwards*: OP v.
  do 3 apply* ok_heap_protochain_write_not_proto.
   apply* ok_heap_protochain_write_proto.
   lets FP: ok_heap_special_function_proto OS.
   do 2 apply* ok_heap_ok_value_write_scope_body.
   do 2 apply* ok_heap_ok_value_write.
  do 4 (apply ok_heap_this_write_not_this; auto_false).
   intros _ M. lets*: fresh_not_indom M.
  apply* ok_heap_function_alloc_fun.
  do 4 apply* ok_heap_null_write.
  do 3 apply* ok_heap_special_write.
    apply* ok_heap_special_write.
    unfolds~ field_normal_prototype.
Qed.

Lemma ok_heap_write_user : forall h l x v,
  ok_value h v ->
  has_some_proto h l ->
  l <> loc_null ->
  ok_heap h ->
  ok_heap (write h l (field_normal x) v).
Proof.
  introv K R L O. lets [OP OL OT OF ON OS]: O.
  constructors.
  apply* ok_heap_protochain_write_not_proto.
   apply* protochain_write_not_proto.
   apply* ok_heap_protochain_def_indom.
  apply* ok_heap_ok_value_write.
  apply* ok_heap_this_write_not_this. auto_false.
  apply* ok_heap_function_write_not_fun.
  apply~ ok_heap_null_write.
  apply~ ok_heap_special_write.
Qed.

Lemma ok_heap_write_fields_user_undef : forall h l ys,
  has_some_proto h l ->
  l <> loc_null ->
  ok_heap h ->
  ok_heap (write_fields h l (map (fun y => (field_normal y, value_undef)) ys)).
Proof.
  introv R L O.
  sets_eq fvs: (map (fun y => (field_normal y, value_undef)) ys).
  gen ys. apply write_fields_ind; clear fvs.
  introv E. auto.
  introv IH E. lets [?|(y&ys'&E')]: (case_last ys);
   subst ys; rew_list in E.
    false* last_eq_nil_inv.
    lets [M1 M2]: last_eq_last_inv (rm E). inverts M2.
    hint has_some_proto_write_fields. apply* ok_heap_write_user.
Qed.

Lemma ok_heap_write_fields_user : forall h l fvs,
  has_some_proto h l ->
  l <> loc_null ->
  ok_heap h ->
  Forall (fun c => let (f, v) := c in
    ok_value h v /\ is_field_normal f) fvs ->
  ok_heap (write_fields h l fvs).
Proof.
  introv R L O.
  apply write_fields_ind.
  auto.
  introv Fu IH. forwards~ ((OV & y & ?) & Fu0): Forall_last_inv IH. subst.
   apply~ ok_heap_write_user.
     inverts~ OV. apply~ ok_value_loc. apply~ has_some_proto_write_fields.
     apply~ has_some_proto_write_fields.
Qed.

Lemma ok_heap_rem : forall h l x,
  ok_heap h ->
  x <> "prototype"%string ->
  ok_heap (rem h l (field_normal x)).
Proof.
  introv [O1 O2 O3 O4 O5 O6] NP. constructors.
  apply* ok_heap_protochain_rem.
  apply* ok_heap_ok_value_rem.
  apply* ok_heap_this_rem.
  apply* ok_heap_function_rem.
  apply* ok_heap_null_rem.
  apply* ok_heap_special_rem.
Qed.

Lemma ok_heap_write_this: forall h h' l l' v,
  ok_heap h ->
  has_null_proto h' l ->
  l <> loc_null ->
  l <> loc_scope ->
  h' = write h l field_this v ->
  v = value_loc l' ->
  has_some_proto h' l' ->
  ok_heap h'.
Proof.
  introv O N NN NS W V P. subst h'.
  lets [OP OL OT OF ON OS]: O. constructors*.
  apply* ok_heap_protochain_write_not_proto.
   subst v. apply* protochain_step. constructor.
  apply* ok_heap_ok_value_write.
   subst v. apply* ok_value_loc. applys* indom_write_inv P.
  subst v. apply* ok_heap_this_write_this.
    unfolds has_null_proto. binds_cases* N.
    unfolds has_some_proto. forwards*: indom_write_inv P.
  apply* ok_heap_function_write_not_fun.
  destruct v; try solve [constructors*|auto_false].
    rewrite V. apply ok_value_loc. applys* indom_write_inv P.
  apply~ ok_heap_null_write.
  apply* ok_heap_special_write.
Qed.

Lemma arguments_ok_value : forall lx lv lfv h,
  arguments lx lv lfv ->
  Forall (ok_value h) lv ->
  Forall (fun c => let (f, v) := c in
    ok_value h v /\ is_field_normal f) lfv.
Proof.
  introv I. induction I; introv F; constructors.
  splits. inverts~ F. exists~ x.
  auto.
  splits. inverts~ F. unfolds*.
  inverts* F.
Qed.

Lemma arguments_for_objects : forall lx lv lfv,
  Forall3 (fun (x : string) (v : value) xv => xv = (field_normal x, v)) lx lv lfv ->
  arguments lx lv lfv.
Proof.
  introv F. induction F.
   constructors.
   subst x3. constructors~.
Qed.

(**************************************************************)
(** ** Tactics for the proof of safety *)

(** Automatisation of [ok_ret_expr] *)

Hint Extern 1 (ok_ret_expr ?h ?r) =>
  match goal with H: context [ok_ret_expr h ?r'] |- _ =>
    let M := fresh in
    assert (M : ok_ret_expr h r'); [ | apply M ]
  end.

(** Automatisation of [extends_proto] *)

Lemma extends_proto_eq_trans : forall h1 h2 h3 h4,
  h3 = h4 ->
  extends_proto h2 h4 ->
  extends_proto h1 h2 ->
  extends_proto h1 h3.
Proof.
  introv E E1 E2. subst. applys extends_proto_trans E2 E1.
Qed.

Lemma extends_proto_write_trans : forall h1 h2 l f v,
  extends_proto h1 h2 ->
  extends_proto h1 (write h2 l f v).
Proof.
  introv H. applys extends_proto_trans H.
  applys extends_proto_write.
Qed.

Lemma extends_proto_write_fields_trans : forall h1 h2 l fvs,
  extends_proto h1 h2 ->
  extends_proto h1 (write_fields h2 l fvs).
Proof.
  introv H. applys extends_proto_trans H.
  applys extends_proto_write_fields.
Qed.

Ltac extends_proto_step :=
  check_noevar_goal;
  first
  [ apply extends_proto_refl
  | apply extends_proto_write_fields_trans
  | apply extends_proto_write_trans
  | applys extends_proto_eq_trans;
    [ eassumption
    | solve [ apply extends_proto_write_fields
            | apply extends_proto_write ]
    | idtac ]
  | match goal with
    | H: context [ extends_proto ?h' ?h] |- extends_proto ?h' ?h =>
        solve [ forwards_nounfold ?: H;
          match goal with
          | |- extends_proto _ _ => solve [ jauto_set; assumption | fail 2 ]
          | |- _ => auto*
          end
       | fail 2 ]
    | H: context [ extends_proto ?h' ?h] |- extends_proto ?h'' ?h =>
       (match h'' with h' => fail 2 | _ => idtac end);
       eapply (@extends_proto_trans h');
        [ idtac
        | solve [ forwards_nounfold ?: H; clear H; auto* | fail 2 ] ]
    end
   ].

Ltac extends_proto_simpl :=
  repeat extends_proto_step.

Hint Extern 1 (extends_proto _ _) => extends_proto_simpl.


(**************************************************************)
(** ** Proof of safety *)

Fixpoint safety_expr h s e o (R : red_expr h s e o) {struct R} :
  ok_heap h ->
  ok_scope h s ->
  ok_ext_expr h e ->
  ok_out_expr h o
with safety_stat h s p o (R : red_stat h s p o) {struct R} :
  ok_heap h ->
  ok_scope h s ->
  ok_ext_stat h p ->
  ok_out_prog h o
with safety_prog h s P o (R : red_prog h s P o) {struct R} :
  ok_heap h ->
  ok_scope h s ->
  ok_ext_prog h P ->
  ok_out_prog h o.
Proof.
  (* safety_expr *)
  induction R; introv O S E.

  (* red_expr_abort *)
  destruct o.
   false.
    (* Martin:  This case is false, but the wrong hypothesis really depends on the expression.
       The following case analysis tries to test all 22 possibilites. *)
    destruct e; simpl in H; inverts H; simpl in E;
      try (inverts E; try (inverts H; fail); try (inverts H1; fail));
      try (inverts H1; inverts H3; fail).
    destruct o0; inverts E.
     inverts H.
     destructs H1. inverts H3.
   inverts H0.
    (* Martin:  Same problem there.  There lacks lemmas about ok_ext_*,
       but I don't think they would be easy to state... *)
    asserts (Oh&Ov&Eh): (ok_heap h /\ ok_value h v /\ extends_proto h0 h).
      destruct e; simpl in H; inverts H; simpl in E;
        try (inverts E; try (inverts H; splits~; fail); try (inverts H1; splits~; fail));
        try (inverts H0; try inverts H2; splits~; fail);
        try (splits~; fail).
      destruct o0; inverts E.
        inverts H. splits~.
        splits~.
      destructs H0. inverts H2. splits~.
    constructors~.

  (* red_ext_res_prog_res_expr_div *)
  inverts* E.
  (* red_ext_res_prog_res_expr_normal *)
  inverts~ E. constructors*.
  (* red_ext_res_prog_res_expr_throw *)
  inverts~ E. constructors*.

  (* red_ext_res_prog *)
  apply* IHR. compute. applys* safety_prog H.

  (* red_expr_ext_list_then *)
  apply* IHR. hint Forall_nil. splits*.

  (* red_expr_ext_list_then_1_nil *)
  apply* IHR. lets (OV & I): E. lets~ C: (rm I) h0 Forall_nil.
  rew_app in C. apply* C.

  (* red_expr_ext_list_then_1_cons *)
  apply* IHR2. forwards~ O1: (rm IHR1).
    destruct o1 as [|h r]. inverts* O1.
    asserts Ext: (extends_proto h0 h).
      inverts* O1.
    split. auto*.
     simpl. splits*.
      applys Forall_trans E.
       hint ok_value_extends. auto*.
      introv FOv. lets (?&E'): E.
       apply* E'.

  (* red_expr_ext_list_then_2 *)
  asserts OK1: (ok_out_expr h0 (out_expr_ter h1 r)).
    inverts~ E.
  asserts Ext: (extends_proto h0 h1).
    inverts~ OK1.
  forwards~: ok_out_expr_extends IHR.
    inverts~ OK1.
    applys~ ok_scope_extends Ext.
    splits*.
     apply* Forall_last.
       apply* E.
       applys~ getvalue_ok_value H; inverts* OK1.
     introv Ext' FOv. rewrite app_last_sym. apply* E.
      apply~ Forall_cons. applys~ ok_value_extends h1.
      inverts~ OK1. applys~ getvalue_ok_value H.
    apply* ok_out_expr_extends.

  (* red_expr_expr_this *)
  hint binds_this_loc_ok_ret_expr. constructors*.

  (* red_expr_expr_variable *)
  hint ok_ret_expr_variable_lookup. constructors*.

  (* red_expr_expr_literal *)
  hint ok_ret_expr_value_of_literal. constructors*.

  (* red_expr_expr_object *)
  lets[o1 o2 o3 o4 o5 [o6 o7 o8 o9]]: O.
  asserts Ext: (extends_proto h0 h1).
    subst h1. apply* extends_proto_write.
  forwards~: ok_out_expr_extends IHR.
    subst h1. apply ok_heap_alloc_obj.
      lets*[v B]: indom_binds o8.
      right*. assumption. assumption.
    subst h1. apply* ok_scope_write.
    compute. introv Ext' FOv. split~.
     applys~ extends_proto_elim h1.
     subst h1. apply~ has_some_proto_write_proto.
    apply* ok_out_expr_extends.

  (* red_expr_expr_object_1 *)
  constructors~.
   subst h1. apply~ ok_heap_write_fields_user.
     inverts~ E.
     inverts~ E. apply* has_some_proto_not_null.
     inverts E. applys~ arguments_ok_value lx H1. (* Martin:  I've used `arguments' there, but I guess I shouldn't have. *)
      apply~ arguments_for_objects.
   subst h1. apply~ ok_ret_expr_loc.
    apply~ has_some_proto_write_fields.
    inverts~ E.

  (* red_expr_expr_function_unnamed *)
  constructors.
    hint ok_heap_protochain, ok_heap_special_obj_proto.
    rewrite H2. apply~ ok_heap_alloc_fun.
      subst h1. apply* ok_scope_write.
      subst h1. indom_simpl_step.
      rewrite H0. apply~ ok_heap_alloc_obj.
        apply* ok_heap_protochain_def_indom.
        right. apply* ok_heap_special_obj_proto.
    subst h2. apply ok_ret_expr_loc. indom_simpl.
    auto*.

  (* red_expr_expr_function_named *)
  asserts: (ok_scope h2 s).
    subst h1 h2. do 2 apply* ok_scope_write.
  constructors.
    hint ok_heap_special_obj_proto.
     asserts O1: (ok_heap h1).
       subst h1. apply~ ok_heap_alloc_obj.
         apply* ok_heap_protochain_def_indom.
         right. apply* ok_heap_special_obj_proto.
     asserts O2: (ok_heap h2).
       subst h2. apply~ ok_heap_alloc_obj.
         apply* ok_heap_protochain_def_indom.
         right. apply* ok_heap_special_obj_proto.
     asserts O3: (ok_heap h3).
       subst h3. apply~ ok_heap_alloc_fun.
         constructors~. subst h2. indom_simpl.
         subst h2 h1. indom_simpl.
     subst h4. applys* ok_heap_write_user.
       apply ok_value_loc. subst h3. indom_simpl.
       subst h3 h2. indom_simpl.
    subst. repeat apply ok_scope_write. auto.
    apply ok_ret_expr_loc. indom_simpl.
    auto.

  (* red_expr_expr_access *)
  apply* IHR2.

  (* red_expr_expr_access_1 *)
  asserts O1: (ok_out_expr h0 (out_expr_ter h1 r)).
    inverts E. constructors~.
  applys ok_out_expr_extends h1.
  inverts~ O1. apply~ IHR2.
    apply* ok_scope_extends.
  forwards~ O2: IHR1.
    apply* ok_scope_extends.
    compute. trivial.
  split~. apply* getvalue_ok_value.
  inverts* O1.

  (* red_expr_expr_access_2 *)
  inverts E. inverts H2. constructors~.
  constructors. right.
  inverts H1.
   inverts H2. false.
   auto*.

  (* red_expr_expr_member *)
  auto*.

  (* red_expr_expr_new *)
  apply* IHR2.

  (* red_expr_ext_expr_new_1 *)
  forwards* O1: IHR.
    inverts* E.
    apply* ok_scope_extends.
      inverts* E.
      compute. constructors*.
        apply* H5. tests: (l2 = loc_obj_proto).
          rewrite TEMP0. inverts* E. apply* ok_heap_special_obj_proto.
          subst l2. destruct* v1. simpl. tests: (l = loc_null).
            false C. simpl. cases_if. reflexivity.
            simpl. cases_if. inverts* E. forwards* OKl: ok_heap_ok_value H3.
             inverts* OKl. inverts* H4.
        splits*.
          constructors*. applys* ok_scope_extends h1. inverts* E.
           lets[_ _ _ OF _ _]: H9. forwards* (s'&x&e&v&B1&_&_&OS): OF.
            forwards* M: binds_func H1 B1. inverts* M.
  inverts E. apply* ok_out_expr_extends.

  (* red_expr_ext_expr_new_2 *)
  asserts O1: (ok_heap h1).
    subst h1. apply~ ok_heap_alloc_obj.
      inverts E. lets (v&B): indom_binds H0. forwards~: ok_heap_protochain B.
      right. inverts* E.
  asserts S1: (ok_scope h1 s). subst h1. apply* ok_scope_write.
  asserts O2: (ok_heap h2).
    subst h2. apply~ ok_heap_alloc_obj. constructor.
  asserts S2: (ok_scope h2 s). subst h2. apply* ok_scope_write.
  asserts O3: (ok_heap h3).
    subst h3. forwards*: ok_heap_write_this h2 l4 l3 l3.
    subst h2. apply~ binds_write_neq. apply* binds_write_eq.
    applys neq_sym. applys~ fresh_binds_neq h1.
    applys~ ok_heap_special_global_this.
    subst h2 h1. do 2 apply~ indom_write. apply* indom_write_eq.
  asserts S3: (ok_scope h3 s). subst h3. apply* ok_scope_write.
  asserts O4: (ok_heap h4).
    subst h4. apply* ok_heap_write_fields_user.
    subst h3 h2 h1. apply~ indom_write. indom_simpl.
    apply* arguments_ok_value. applys~ Forall_trans value (ok_value h0).
     introv Oa. applys~ ok_value_extends h0. inverts* E.
  asserts S4: (ok_scope h4 s). subst h4. apply* ok_scope_write_fields.
  asserts O5: (ok_heap h5).
    subst h5. apply* ok_heap_write_fields_user_undef.
    subst h4 h3 h2. apply~ indom_write_fields.
     apply~ indom_write. apply* indom_write_eq.
  asserts S5: (ok_scope h5 s). applys* ok_scope_extends.
  asserts S5': (ok_scope h5 (l4 :: s3)). constructors~.
    applys ok_scope_extends. inverts~ E. lets (A&B): H9.
     inverts* A. extends_proto_simpl.
    subst h5 h4 h3 h2. apply~ has_some_proto_write_fields.
     apply* indom_write_fields. apply~ has_some_proto_write.
      apply* indom_write_eq.
  asserts PH: (has_some_proto h1 l3). subst h1. apply* indom_write_eq.
  asserts~: (extends_proto h1 h5).
  forwards~ HQ: IHR1.
  forwards~ HZ: IHR2. constructors~. destruct~ o1.
    inverts* HQ.
  apply* ok_out_expr_extends.

  (* red_expr_ext_expr_new_3 *)
  inverts* E. inverts* H2. constructors~.
  apply* obj_of_value_ok_ret_expr.

  (* red_call *)
    (* abort o1 case *)
    apply* IHR2.

    (* ext_expr_call_1 and 2 *)
    forwards~ H_ok_ext: IHR.
      (* ok_heap case *)
      inverts E.
      apply H3.

      (* ok_scope case *)
      inverts E.
      inverts S.
        (* singleton case *)
        constructor.

        (* list case *)
        constructor.
          (* premise: ok_scope *)
          applys* ok_scope_extends h0.
          (* premise: has_some_proto *)
          apply* H5.

      (* ok_ext_expr case *)
      constructor.
        (* premise l1 has proto *)
        inverts R.
          (* abort case *)
          false H1.

          (* non-eval case *)
          inverts E.
          forwards~ P: ok_heap_protochain H7.
          inverts P.
            (* null case*)
            forwards~ P:ok_heap_null H7.

            (* non-null case *)
            apply binds_indom in H1.
            unfold has_some_proto.
            trivial.

          (* eval case *)
          inverts E.
          (* apply H5. *)
          (* inverts O. *)
          (* inverts ok_heap_special. *)
          inverts H.
            inverts H4.
            inverts H1.
              inverts H0.

              inverts H.

            trivial.


            forwards~ P:ok_heap_ok_value H8.
            invert P.
              (* value case *)
              introv FALSE.
              inverts FALSE.

              (* loc case *)
              intros.
              trivial.
        (* premise l2 has proto *)
        subst l2.
        destruct r1.
          (* value *)
          compute.
          inverts E.
          apply* ok_heap_special_global_proto.

          (* location *)
          destruct r.
          compute.
          cases_if.
            (* global *)
            inverts E.
            apply* ok_heap_special_global_proto.

            (* regular *)
            inverts H.
            inverts H3.
              (* case 1: notin *)
              congruence.
              (* case 2: here *)
              inverts E.
              forwards~ P:ok_heap_protochain H8.
              inverts H5.
              destruct* H2.

              (* case 3: next*)
              apply binds_indom in H1.
              trivial.

      (* Back to the point: ok_out_expr *)
      inverts E.
      applys* ok_out_expr_extends.

    (* ext_expr_call_3 *)
    apply* IHR.

    compute.
    intros.
    split.
      (* 1st Conjunct *)
      apply* H2.
      destruct E.
      apply H5.


      split~.
      (* 2nd Conjunct *)
      apply* ok_body_or_primitive_normal_body.
      assert (ok_h0 : ok_scope h0 s3).
        (* Proving assertion *)
        forwards~ P: ok_heap_function O.
        forwards*: P.
        lets (s2&x&e&v'&B1&B2&B3&O2): (rm H4).
        forwards* M: binds_func H0 B1. inverts M.
        apply O2.

        (* Back to the point *)
        applys~ ok_scope_extends ok_h0.


    (* ext_expr_call_3 *)
    applys* IHR.
    compute. split.
      apply H.
      destruct E.
      apply H2.

      split*.
        apply (ok_body_or_primitive_primitive h' primitive_eval).

    (*  red_expr_ext_expr_call_3 *)
    asserts O1: (ok_heap h1). subst h1. apply~ ok_heap_alloc_obj. constructor.
    asserts S1: (ok_scope h1 s). subst h1. apply* ok_scope_write.
    asserts O2: (ok_heap h2).
      subst h2. forwards*: ok_heap_write_this h1 l1 l0 l0.
      subst h1. apply~ binds_write_neq. apply* binds_write_eq.
      applys neq_sym. applys~ fresh_binds_neq h0.
      applys~ ok_heap_special_global_this. inverts~ E.
      subst h1. do 2 apply* indom_write.
    asserts S2: (ok_scope h2 s). subst h2. apply* ok_scope_write.
    asserts O3: (ok_heap h3).
      subst h3. apply* ok_heap_write_fields_user.
      subst h2 h1. apply~ indom_write. indom_simpl.
      apply* arguments_ok_value. applys~ Forall_trans value (ok_value h0).
      introv Oa. applys~ ok_value_extends h0. inverts* E.
    asserts S3: (ok_scope h3 s). subst h3. apply* ok_scope_write_fields.
    asserts O4: (ok_heap h4).
      subst h4. apply* ok_heap_write_fields_user_undef.
      subst h3 h2 h1. apply~ indom_write_fields.
      apply~ indom_write. apply* indom_write_eq.
    asserts S4: (ok_scope h4 s). subst h4. apply* ok_scope_write_fields.
    asserts S5: (ok_scope h4 (l1 :: s3)). constructors~.
      applys ok_scope_extends. inverts~ E. lets (A&B): H7.
      inverts* A. extends_proto_simpl. subst h4 h3 h2 h1.
      do 2 apply~ has_some_proto_write_fields. apply~ has_some_proto_write.
      apply* indom_write_eq.
    forwards~ OMG: IHR2.
      apply~ IHR1.
        constructors*.
      apply* ok_out_expr_extends.


    (* ext_expr_call_4 *)
    applys* IHR2.
    compute.
    apply* IHR1.
      (* ok_ext_expr *)
      inverts~ E.
      elim H1. clear H1. intros.
      compute.
      trivial.

    (* ext_expr_call_4 - non abort case *)
    inverts* E. constructors*.

  (* red_expr_expr_unary_op *)
  apply~ IHR2.
    constructor*.

  (* red_expr_ext_expr_unary_op_1 *)
  inverts~ E. inverts~ H2. constructors~. inverts* H0.

  (* red_expr_ext_expr_unary_op_1_typeof_value *)

  inverts~ E.
  inverts~ H2.
  constructor*.

  inverts~ E. inverts~ H0. constructors*.

  (* red_expr_ext_expr_unary_op_1_pre_incr *)
  inverts~ E.  inverts~ H3. constructors~.
    subst h2. unfold update. case_if.
      apply~ ok_heap_write_user.
        inverts* H0.
        apply* ok_heap_special_global_proto. congruence.
      apply~ ok_heap_write_user.
        inverts* H0.
        inverts* H7.
    inverts* H0.

  (* red_expr_ext_expr_unary_op_1_pre_decr *)
  inverts~ E.
  constructor*.
    (* ok_heap *)
    inverts H3.
    subst.
    unfold update.
    cases_if.
      (* global *)
      applys* ok_heap_write_user.
        (* ok_value *)
        constructor.
        inverts* H0.

        (* has_some_proto *)
        apply* ok_heap_special_global_proto.

        (* global non null *)
        compute.
        introv FALSE.
        inverts FALSE.

      (* non-global *)
      applys* ok_heap_write_user.
        (* ok_value *)
        constructor.
        inverts* H0.

        (* has_some_proto *)
        inverts* H7.

    (* ok_ret_expr *)
    constructor.
    constructor.
    inverts* H0.

    (* extends_proto *)
    inverts* H3.


  (* red_expr_ext_expr_unary_op_1_post_incr *)
  inverts~ E. inverts~ H3. constructors~.
    subst h2. unfold update. case_if.
      apply~ ok_heap_write_user.
        inverts* H0.
        apply* ok_heap_special_global_proto. congruence.
      apply~ ok_heap_write_user.
        inverts* H0.
        inverts* H7.
    inverts* H0.

  (* red_expr_ext_expr_unary_op_1_post_decr *)
  inverts~ E. inverts~ H3. constructors~.
    subst h2. apply~ ok_heap_write_user.
      inverts* H0.
      case_if.
        apply* ok_heap_special_global_proto.
        inverts* H7.
      case_if~. congruence.
      inverts* H0.


  (*  red_expr_ext_expr_unary_op_1_delete_true *)
  inverts* E. constructor.
    (* ok_heap *)
    inverts* H2.
    subst h2.
    destruct r.
      (* value *)
      trivial.
      (* ref *)
      destruct r.

      destruct f; inverts* H6.
        (* normal *)
        applys* ok_heap_rem.
        intro.
        contradiction H.
        repeat right.
        inverts* H0.

    (* ok_ret_expr *)
    inverts* H2.

    (* extends_proto *)
    subst h2. destruct r; inverts* H2.
    destruct r. destruct f; inverts* H5.
    applys~ extends_proto_trans h1.
    apply extends_proto_rem. inverts* H2.

  (* red_expr_ext_expr_unary_op_1_delete_false *)
  inverts~ E. inverts~ H1. constructors*.

  (* ext_expr_binary_op_1 *)
  apply~ IHR2.
  constructors*.


  (* ext_expr_binary_op_2  -- In two cases*)
    (* Case 1 *)
    asserts O1: (ok_out_expr h0 (out_expr_ter h1 r)).
      inverts* E.
    applys ok_out_expr_extends h1.
      inverts~ O1. apply~ IHR.
        apply* ok_scope_extends.
        destruct ov; compute.
          inverts~ H0; constructors*.
          split~. applys* getvalue_ok_value.
      inverts* O1.

    (* Case 2 *)
    inverts~ E; constructors*.

    (* ext_expr_binary_op_2_none *)
    apply~ IHR2. forwards~ O1: IHR1.
    inverts O1.
    splits~.
      inverts~ E.
       applys~ ok_value_extends H2.
      constructors~.
    splits~.
      inverts~ E.
       applys~ ok_value_extends H2.
      constructors~.

   (* ext_expr_binary_op_3 *)
   lets[H1 [_ H2]]: E. inverts~ H2. constructors~. inverts* H0.
    apply* ok_ret_expr_instanceof_red.


  (* RED_assign in 5 cases *)
    (* Case 1: ext_expr_assign_1 *)
    apply~ IHR2.
    compute.
    destruct op.
      split~.
      apply* IHR1.

    (* Case 2: ext_expr_assign_2 re *)
    asserts O1: (ok_out_expr h0 (out_expr_ter h1 re)).
      inverts E. constructors~.
    applys ok_out_expr_extends h1; inverts~ O1.
    apply~ IHR2.
      apply* ok_scope_extends.
      forwards~ O2: IHR1.
        apply* ok_scope_extends.
      constructors~. inverts~ O2.
       compute. inverts* H2.
       compute. inverts* H2.

    (* Case 3: ext_expr_assign_2 Ref *)
    inverts~ E. inverts~ H2. constructors~.
      subst h2. apply~ ok_heap_write_user.
        inverts~ H.
          inverts* H6.
          apply* ok_heap_ok_value.
        case_if.
          apply* ok_heap_special_global_proto.
          inverts* H1.
        case_if~. congruence.
      inverts~ H.
        inverts H6. constructor. applys* ok_value_extends h1.
        constructor. applys~ ok_value_extends h1. apply* ok_heap_ok_value.


    (* Case 4: ext_expr_assign_2_op r *)
    asserts O1: (ok_out_expr h0 (out_expr_ter h1 r)).
      inverts* E.
    applys ok_out_expr_extends h1; inverts~ O1.
    apply~ IHR2.
      apply* ok_scope_extends.
      forwards~ O2: IHR1.
        apply* ok_scope_extends.
      constructor~. inverts~ O2. compute. inverts* H3. compute. inverts* H3.
      splits~.
      destruct o2. compute. applys* getvalue_ok_value.
      compute. applys~ ok_value_extends h1. applys* getvalue_ok_value.
      inverts* O2.

    (* Case 5: ext_expr_assign_2_op Ref *)
    inverts~ E. destruct H3 as [O1 [O2 O3]]. inverts~ O3.
    constructors~.
      subst h2. apply~ ok_heap_write_user.
        simpl in O1.
        apply ok_ret_expr_binary_op_red with op v1 v2 v h1 in O1.
          inverts* O1.
          applys* getvalue_ok_value.
          trivial.
        case_if.
          apply* ok_heap_special_global_proto.
          inverts* H2.
        case_if~. congruence.
      constructors~.
      apply ok_ret_expr_binary_op_red with op v1 v2 v h1 in O1.
        inverts~ O1. applys* ok_value_extends h1.
        applys* getvalue_ok_value.
        trivial.

  (* safety_stat *)
  induction R; introv O S E.

  (* red_stat_abort *)
  destruct o.
   false.
    (* Martin:  Same problem as before (see red_expr_abort). *)
    destruct p; simpl in H; inverts H; simpl in E;
      inverts E.
    inverts H.
   asserts (Oh&Eh): (ok_heap h /\ extends_proto h0 h).
      destruct p; simpl in H; inverts H; simpl in E;
        inverts E; try (splits~; fail).
      inverts H; splits~.
    inverts H1; constructors~.
      destruct p; simpl in H; inverts H; simpl in E; inverts~ E.
       inverts~ H.
      destruct p; simpl in H; inverts H; simpl in E; inverts~ E.
       inverts~ H.

  (* red_ext_res_expr_res_prog_div *)
  inverts* E.
  (* red_ext_res_expr_res_prog_normal *)
  inverts~ E. constructors*.
  (* red_ext_res_expr_res_prog_throw *)
  inverts~ E. constructors*.

  (* red_ext_stat_expr *)
  apply~ IHR. compute. applys* safety_expr H.

  (* red_stat_stat_expr *)
  auto*.

  (* red_stat_stat_seq *)
  apply~ IHR2. forwards~ O1: IHR1.

  (* red_stat_stat_seq_1 *)
  inverts E. forwards~ O1: IHR.
    apply* ok_scope_extends.
  apply* ok_out_prog_extends.

  (* red_stat_stat_var_decl *)
  constructors~.

  (* red_stat_stat_var_decl_expr *)
  apply~ IHR2. forwards~ O1: IHR1.

  (* red_stat_stat_var_decl_expr_1 *)
  inverts E. constructors~.

  (* red_stat_stat_if *)
  apply~ IHR2. forwards~ O1: IHR1.

  (* red_stat_stat_if_1_true *)
  inverts E. applys~ ok_out_prog_extends H5.
  apply~ IHR.
    apply* ok_scope_extends.
    compute. trivial.

  (* red_stat_stat_if_1_false *)
  inverts E. applys~ ok_out_prog_extends H5.
  apply~ IHR.
    apply* ok_scope_extends.
    compute. trivial.

  (* red_stat_stat_if_1_false_implicit *)
  inverts E. constructors~.

  (* red_stat_stat_while *)
  apply~ IHR2. forwards~ O1: IHR1.


  (* red_stat_stat_while_1_false *)
  inverts E. constructors~.

  (* red_stat_stat_while_1_true *)
  inverts E. applys~ ok_out_prog_extends H5.
  apply~ IHR2.
    apply* ok_scope_extends.
    apply~ IHR1.
      applys~ ok_scope_extends S.
      compute. trivial.

  (* red_stat_stat_while_2 *)
  inverts E. applys~ ok_out_prog_extends H3.
  apply~ IHR.
    applys~ ok_scope_extends S.
    compute. trivial.

  (* red_stat_stat_with *)
  apply~ IHR2. forwards~ O1: IHR1.

  (* red_stat_stat_with_1 *)
  inverts E. applys~ ok_out_prog_extends H5.
  apply~ IHR.
    constructors.
      applys~ ok_scope_extends H5.
      forwards~ Ol: getvalue_ok_value H.
    compute. trivial.

  (* red_stat_stat_throw *)
  apply~ IHR2. compute. apply~ IHR1.

  (* red_stat_ext_stat_throw_1 *)
  inverts E. constructors~. apply* getvalue_ok_value.

  (* red_stat_ext_stat_try *)
  apply~ IHR2. compute. apply~ IHR1.

  (* red_stat_ext_stat_try_1_no_catch *)
  apply~ IHR.

  (* red_stat_ext_stat_try_1_finally *)
  apply~ IHR.

  (* red_stat_ext_stat_try_1_catch *)
  inverts E.
  asserts O2: (ok_heap h2).
    subst h2. inverts H4. inverts ok_heap_special.
    apply~ ok_heap_alloc_obj.
      forwards~ (p&P): indom_binds ok_heap_special_obj_proto.
       apply* ok_heap_protochain.
      repeat constructors~.
  asserts Ext2: (extends_proto h1 h2).
    subst h2. apply* extends_proto_write_trans.
  asserts O3: (ok_heap h3).
    subst h3. apply~ ok_heap_write_user.
      apply* ok_value_extends.
      subst. apply* indom_write_eq.
      apply* fresh_not_null.
  asserts Ext3: (extends_proto h2 h3).
    subst h3. apply* extends_proto_write_trans.
  asserts S3: (ok_scope h3 (l0::s)).
    constructors~. applys~ ok_scope_extends h2.
     applys~ ok_scope_extends h1. apply* ok_scope_extends.
    subst h3 h2. indom_simpl.
  forwards* OK: IHR.
  applys~ ok_out_prog_extends h1.
  applys~ ok_out_prog_extends h2.
  applys~ ok_out_prog_extends h3.

  (* red_stat_ext_stat_try_2 *)
  asserts S0: (ok_scope h0 s1).
    apply* E.
  apply~ IHR2. simpl. apply~ IHR1. simpl. trivial.

  (* red_stat_ext_stat_try_3_none *)
  auto*.

  (* red_stat_ext_stat_try_3_some *)
  asserts (O1&Ext): (ok_heap h1 /\ extends_proto h0 h1).
    splits; inverts~ E.
  applys~ ok_out_prog_extends h1.
  asserts S1: (ok_scope h1 s).
    apply* ok_scope_extends.
  apply~ IHR2. splits.
   apply~ IHR1. simpl. trivial.
   destruct r; constructors~; inverts~ E.

  (* red_stat_ext_stat_try_4_normal *)
  inverts E.
  asserts Ext: (extends_proto h0 h1).
    inverts~ H.
  asserts O1: (ok_heap h1).
    inverts~ H.
  destruct r; constructors~.
    inverts~ H0.
     inverts H4. constructors~.
     apply* ok_value_extends.
     inverts* H0.
    inverts~ H0. inverts~ H4.
     apply~ ok_ret_expr_value.
       applys~ ok_value_extends h0.
     apply~ ok_ret_expr_ref.
       inverts* H0.
    inverts~ H0.
      applys~ ok_value_extends h0.


  (* red_stat_stat_skip *)
  constructors~.


  (* safety_prog *)
  induction R; introv O S E.

  (* red_prog_abort *)
  destruct~ P; inverts~ H.

  (* red_prog_stat *)
  apply* safety_stat.

  (* red_prog_prog_seq *)
  apply~ IHR2. forwards~ O1: IHR1.

  (* red_prog_prog_seq_1 *)
  inverts E. forwards~ O1: IHR.
    apply* ok_scope_extends.
  apply* ok_out_prog_extends.

Qed.

End Safety.

