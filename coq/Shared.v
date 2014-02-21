Set Implicit Arguments.
Require Export LibTactics LibCore LibString LibFset LibSet.
Generalizable Variables A B.
Require Export LibProd LibListZ.


(**************************************************************)
(** ** Notation to force "if" to be on booleans 
       (and never on decidable equalities). *)

Notation "'if' b 'then' v1 'else' v2" :=
  (if (b : bool) then v1 else v2)
  (at level 200, right associativity) : type_scope.


(**************************************************************)
(** Auxiliary function to perform case analysis on an option 
    without requiring an explicit match. *)

Definition option_case {A B : Type} (d : B) (f : A -> B) (op : option A) : B :=
  match op with
  | None => d
  | Some x => f x
  end.


(**************************************************************)
(** ** Char-related functions *)

(* Note that string is extracted to "char list" in Ocaml *)

(* Int_of_char is currently directly extracted in Caml as:
     "(fun c -> float_of_int (int_of_char c))". 
   No property of this function is currently needed. *)

Parameter int_of_char : Ascii.ascii -> int.

(* Comparison on Ascii characters implemented as (=) on "char" in Caml *)

Parameter ascii_compare : Ascii.ascii -> Ascii.ascii -> bool.
Parameter ascii_compare_beq : forall (x y : Ascii.ascii),
  (ascii_compare x y) <-> (x = y).

Global Instance ascii_comparable : Comparable Ascii.ascii.
Proof.
  applys (comparable_beq ascii_compare).
  applys ascii_compare_beq.
Qed.


(**************************************************************)
(** ** String-related functions *)

(** Binding for Coq stdlib concatentation function *)

Definition string_concat : string -> string -> string :=
  String.append.

(** Binding for Coq stdlib substring function *)

Definition string_sub s (n l : int) : string :=
  substring (abs n) (abs l) s.


(**************************************************************)
(** ** Operators specific *)

Global Instance op_unary_inhab : forall P : Type,
  Inhab (P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.

Global Instance op_binary_inhab : forall P : Type,
  Inhab (P -> P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.


(**************************************************************)
(** ** Extraction for comparison operators on integers *)

Definition comparison_compare c1 c2 :=
  match c1, c2 with
  | Datatypes.Eq, Datatypes.Eq => true
  | Datatypes.Lt, Datatypes.Lt => true
  | Datatypes.Gt, Datatypes.Gt => true
  | _, _ => false
  end.

Global Instance comparison_comparable : Comparable comparison.
Proof.
  applys (comparable_beq comparison_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H; tryfalse; try congruence; auto.
Qed.

(* Directly extracted towards (<) in OCaml *)

Global Instance lt_int_decidable : forall i1 i2 : int, Decidable (i1 < i2).
Proof.
  intros. applys decidable_make (decide (i1 ?= i2 = Datatypes.Lt)).
  rewrite lt_zarith. unfold Z.lt. rew_refl. reflexivity.
Qed.

(* Directly extracted towards (<=) in OCaml *)

Global Instance le_int_decidable : forall i1 i2 : int, Decidable (i1 <= i2).
Proof.
  intros. applys decidable_make (decide (i1 ?= i2 <> Datatypes.Gt)).
  rewrite le_zarith. unfold Z.le, Z.lt. rew_refl. fequals.
Qed.

(* Directly extracted towards (>=) in OCaml *)

Global Instance ge_nat_decidable : forall n1 n2 : nat, Decidable (n1 >= n2).
Proof.
  intros. applys sumbool_decidable. applys Compare_dec.ge_dec.
Qed.


(**************************************************************)
(* To be added to LibInt or LibNat *)

Lemma nat_int_le : forall (x y:nat),
  x <= y -> ((x:int) <= (y:int)).
Proof. math. Qed.

Lemma nat_int_ge : forall (x y:nat),
  x >= y -> ((x:int) >= (y:int)).
Proof. math. Qed.


(**************************************************************)
(* To be added to LibListZ *)

Lemma ZNth_to_Nth : forall A (n : nat) x (l : list A),
  LibListZ.ZNth n l x -> LibList.Nth n l x.
Proof. introv (H&_). rewrite~ abs_pos_nat in H. Qed.

Lemma Nth_to_ZNth : forall A (n : nat) x (l : list A),
  LibList.Nth n l x -> LibListZ.ZNth n l x.
Proof. introv H. splits*. rewrite~ abs_pos_nat. math. Qed.


(**************************************************************)
(* To be added to LibList *)

Lemma length_Nth_lt : forall A n (l : list A),
  n < LibList.length l -> exists x, Nth n l x.
Proof.
  induction n; introv Comp; destruct l as [|a l'];
    rew_list in Comp; try solve [math].
   eexists. apply Nth_here.
   simpls. rewrite lt_SS in Comp.
    forwards (x&Hx): IHn Comp. exists x.
    apply* Nth_next.
Qed.


(**************************************************************)
(** ** Generalization of Pickable to function that return options *)

(* Note: easier to use Pickable_option than Pickable directly. *)

Class Pickable_option (A : Type) (P : A -> Prop) := pickable_option_make {
  pick_option : option A;
  pick_option_correct : forall a, pick_option = Some a -> P a;
  pick_option_defined : (exists a, P a) -> (exists a, pick_option = Some a) }.

Implicit Arguments pick_option [A [Pickable_option]].
Extraction Inline pick_option.

Global Instance Pickable_option_Pickable : 
  forall (A : Type) (P : A -> Prop), Inhab A -> (* later: use `{Inhab A} *)
  Pickable_option P -> Pickable P.
Proof.
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


(***********************************************************)
(***********************************************************)
(***********************************************************)
(** * Heap with a counter for allocating fresh locations *)

Require Import LibHeap.
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


(**************************************************************)
(* To be added to LibRelation *)

Require Export LibRelation.

Lemma tclosure_tclosure' : forall A (R : binary A) x y,
  tclosure R x y <-> tclosure' R x y.
Proof.
  introv. iff C.
   destruct C as [x y z HR HC]. gen x. induction HC; introv HR.
    apply~ tclosure'_step.
    applys~ tclosure'_trans x. constructors~.
   induction C.
    constructors*. constructors~.
    apply* tclosure_trans.
Qed.

Lemma tclosure_ind_right : forall A (R : binary A) (P : A -> A -> Prop),
  (forall x y, R x y -> P x y) ->
  (forall y x z, tclosure R x y -> P x y -> R y z -> P x z) ->
  forall x y, tclosure R x y -> P x y.
Proof.
  introv S Ind H. inverts H as HR HC.
  induction HC using rtclosure_ind_right.
   apply* S.
   apply* Ind. apply* tclosure_step_rtclosure.
Qed.

Lemma tclosure_right : forall A (R : binary A) x y,
  tclosure R x y ->
  exists z, rtclosure R x z /\ R z y.
Proof.
  introv H. induction H using tclosure_ind_right.
   exists x. splits~. constructors~.
   exists y. splits~. apply~ tclosure_rtclosure.
Qed.

Lemma rtclosure_le : forall A (R1 R2 : binary A),
  incl R1 R2 -> incl (rtclosure R1) (rtclosure R2).
Proof. introv Incl HC. induction HC; constructors*. Qed.

Lemma tclosure_tclosure_step : forall A (R : binary A) x y z,
       tclosure R x y -> R y z -> tclosure R x z.
Proof. intros. apply* tclosure_rtclosure_step. apply* tclosure_rtclosure. Qed.

Lemma tclosure_le : forall A (R1 R2 : binary A),
  incl R1 R2 -> incl (tclosure R1) (tclosure R2).
Proof.
  introv Incl HC. induction HC using tclosure_ind_right.
   apply* tclosure_once.
   apply* tclosure_tclosure_step.
Qed.

