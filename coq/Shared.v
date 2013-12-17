Set Implicit Arguments.
Require Export LibTactics LibCore LibString LibFset LibSet.
Generalizable Variables A B.
Require Export LibProd.


(**************************************************************)
(** ** Notation to force "if" to be on booleans 
       (and never on decidable equalities). *)

Notation "'if' b 'then' v1 'else' v2" :=
  (if (b : bool) then v1 else v2)
  (at level 200, right associativity) : type_scope.


(**************************************************************)
(** ** String-related functions *)

(* todo: extract in a more clever way ! *)
Parameter int_of_char : Ascii.ascii -> int.

Definition string_sub s (n l : int) : string :=
  substring (abs n) (abs l) s.

Axiom ascii_compare : Ascii.ascii -> Ascii.ascii -> bool.

Global Instance ascii_comparable : Comparable Ascii.ascii.
Proof. applys (comparable_beq ascii_compare). skip. Qed. (* TODO:fix *)

(* todo: implement using lib *)
Parameter string_concat : string -> string -> string.

(* MARTIN: is this used anywhere ? *)
Parameter is_substring : string -> string -> Prop.
Parameter is_substring_dec : forall s1 s2, Decidable (is_substring s1 s2).


(**************************************************************)
(** ** Operators specific *)

Global Instance op_unary_inhab : forall P : Type,
  Inhab (P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.

Global Instance op_binary_inhab : forall P : Type,
  Inhab (P -> P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.


(**************************************************************)
(** ** Generalization of Pickable to function that return options *)

(* MARTIN: see whether it is possible to use Pickable directly *)

(** Pickable for option types *)

Class Pickable_option (A : Type) (P : A -> Prop) := pickable_option_make {
  pick_option : option A;
  pick_option_correct : forall a, pick_option = Some a -> P a;
  pick_option_defined : (exists a, P a) -> (exists a, pick_option = Some a) }.

Implicit Arguments pick_option [A [Pickable_option]].
Extraction Inline pick_option.

Global Instance Pickable_option_Pickable : 
  forall (A : Type) (P : A -> Prop), Inhab A -> (* todo: use `{Inhab A} *)
  Pickable_option P -> Pickable P.
Proof.
  (* todo: clean up proof *)
  introv I [[pi|] C D].
   applys pickable_make pi. introv _. apply~ C.
   applys pickable_make arbitrary. introv E. forwards (a&N): D E. inverts N.
Qed.

(** Application to LibHeap operation *)

Require Import LibHeap.

Global Instance binds_pickable_option : forall K V : Type,
  `{Comparable K} -> `{Inhab V} ->
  forall (h : heap K V) (v : K),
  Pickable_option (binds h v).
Proof.
  introv CK IV; introv. applys pickable_option_make (read_option h v).
   apply read_option_binds. 
   introv [a Ba]. forwards R: @binds_read_option Ba. exists~ a.
Qed.

(**************************************************************)
(** ** MARTIN: why do we need these? *)

Axiom int_lt_dec : forall k1 k2 : int, Decidable (k1 < k2).

Global Instance le_int_decidable : forall i1 i2 : int, Decidable (i1 <= i2).
Admitted.

Global Instance ge_nat_decidable : forall n1 n2 : nat, Decidable (n1 >= n2).
Admitted.



(**************************************************************)
(** ** MARTIN: do we still need this operation? Haven't we given it a better name? *)

Definition morph_option {B C : Type} (c : C) (f : B -> C) (op : option B) : C :=
  match op with
  | None => c
  | Some b => f b
  end.

(* MARTIN: does not seem to be used *)
Definition unmonad_option {B : Type} (default : B) (op : option B) : B :=
  morph_option default id op.


(**************************************************************)
(** ** MARTIN: where do we use this? *)

Class FunctionalPred A (P:A->Prop) := functionalpred_make {
    functional_pred : forall x y, P x -> P y -> x = y }.

Global Instance apply_if_exists_pickable :
  forall (A B : Type) (P : A -> Prop) (f : A -> B),
  Pickable P -> FunctionalPred P ->
  Pickable (fun v => exists x, P x /\ f x = v).
Proof.
  introv [p Hp] [F]. applys pickable_make (f p).
  intros (a & x & (Hx & Ha)). exists x. splits~.
  forwards*: F Hx Hp. substs~.
Qed.

Global Instance binds_functionnal : forall (H K : Type) (h : heap H K) k,
  Comparable H -> Inhab K ->
  FunctionalPred (binds h k).
Proof. introv C I. applys functionalpred_make. apply binds_func. Qed.
(* End of this little test. *)


(**************************************************************)

(* MARTIN: modifier l'interpréteur
  pour utiliser une fonction qui fasse 
  last et removelast en même temps:
  cf.   LibList.take_drop_last.
  
  Ensuite, supprimer le lemme ci-dessous *)

Lemma length_removelast : forall A (l : list A),
  l <> nil ->
  LibList.length (removelast l) = (LibList.length l - 1)%nat.
Proof.
  introv. destruct~ l. introv _. gen a. induction~ l. introv.
  unfold removelast. fold (removelast (a :: l)).
  do 2 rewrite length_cons. rewrite IHl. simpl.
  rewrite* LibNat.minus_zero.
Qed.


(**************************************************************)
(** ** MARTIN: remplacer "In" par "Mem",; 
   J'ai ajouté Mem_decidable. On pourra alors supprimer les defs ci dessous *)

Fixpoint mem_decide (A : Type) `{Comparable A} (x : A) (l : list A) :=
  match l with
  | nil => false
  | y::l' => ifb x = y then true else mem_decide x l'
  end.

Lemma mem_decide_eq_mem : forall A (H : Comparable A) (x : A) l,
  mem_decide x l = LibList.mem x l.
Proof.
  induction l.
   auto.
   simpl. case_if.
     rewrite~ eqb_eq.
     rewrite~ eqb_neq. rewrite~ neutral_l_or.
Qed.

Global Instance In_decidable : forall A : Type,
  Comparable A ->
  forall (x : A) l, Decidable (In x l).
Proof.
  introv CA. intros.
  applys decidable_make (mem_decide x l).
  rewrite mem_decide_eq_mem.
  induction l.
    simpl. rew_refl~.
    tests: (a = x); simpl; rew_refl.
      rewrite eqb_self. simpl. reflexivity.
      do 2 rewrite~ eqb_neq. rewrite~ IHl.
Qed.



(***********************************************************)
(***********************************************************)
(***********************************************************)
(** * Heap with a counter for allocating fresh locations *)

(* MARTIN: j'ai du mal à comprendre comment ça peut marcher. *)

Module HeapGen (Export Heap : HeapSpec) : HeapSpec.
Generalizable Variable K V.

Definition heap K V := (nat * heap K V)%type.

Section HeapDefs.
(*Variables K V : Type.*)
Context `{Comparable K} `{Inhab V}.
Definition empty : heap K V := (0%nat, empty).
Definition dom (h : heap K V) := dom (snd h).
Definition binds (h : heap K V) := binds (snd h).
Definition to_list (h : heap K V) := to_list (snd h).
Definition read (h : heap K V) := read (snd h).
Definition write (h : heap K V) k v :=
  let (id, h0) := h in
  (S id, write (snd h) k v).
Definition rem (h : heap K V) k :=
  let (id, h0) := h in
  (S id, rem (snd h) k).
Definition indom (h : heap K V) := indom (snd h).
Definition read_option (h : heap K V) := read_option (snd h).
End HeapDefs.

Section HeapAxioms.
Context `{Comparable K} `{Inhab V}.
Implicit Types h : heap K V.

Lemma indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).
Proof. destruct h. eapply indom_equiv_binds. Qed.

Lemma dom_empty :
  dom (@empty K V) = \{}.
Proof. unfold empty. eapply dom_empty. Qed.

Lemma binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).
Proof. destruct h. eapply binds_equiv_read. Qed.

Lemma dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.
Proof. destruct h. eapply dom_write. Qed.

Lemma binds_write_eq : forall h k v,
  binds (write h k v) k v.
Proof. destruct h. eapply binds_write_eq. Qed.

Lemma binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' -> 
  binds (write h k' v') k v.
Proof. destruct h. eapply binds_write_neq. Qed.

Lemma binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v -> 
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v). 
Proof. destruct h. eapply binds_write_inv. Qed.

Lemma binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.
Proof. destruct h. eapply binds_rem. Qed.

Lemma binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.
Proof. destruct h. eapply binds_rem_inv. Qed.

Lemma not_indom_rem : forall h k,
  ~ indom (rem h k) k.
Proof. destruct h. eapply not_indom_rem. Qed.

Lemma binds_equiv_read_option : forall h k v,
  (binds h k v) = (read_option h k = Some v).
Proof. destruct h. eapply binds_equiv_read_option. Qed.

Lemma not_indom_equiv_read_option : forall h k,
  (~ indom h k) = (read_option h k = None).
Proof. destruct h. eapply not_indom_equiv_read_option. Qed.

Lemma read_option_def : forall h k,
  read_option h k = (If indom h k then Some (read h k) else None).
Proof. destruct h. eapply read_option_def. Qed.

Lemma indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Proof. destruct h. eapply indom_decidable. Qed.

End HeapAxioms.

End HeapGen.
