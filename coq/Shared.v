Set Implicit Arguments.
Require Export LibTactics LibCore LibString LibFset LibSet.
Generalizable Variables A B.
Require Export LibProd.

(** This file contains lots of definitions that will all get
    merged in the TLC library, a general-purpose library for Coq. *)

(**************************************************************)
(** ** LATER: move to LibTactics *)

Ltac decompose_base X I :=
  gen ltac_mark; gen X; intros X;
  let Y := fresh in set (Y:=X); destruct X as I; rename Y into X;
  intro_until_mark.

Tactic Notation "decompose" ident(E) "as" simple_intropattern(I) :=
  decompose_base E I.





Definition let_binding (A B:Type) (v:A) (K:A->B) := K v.

Notation "'Let' x ':=' v 'in' e" := (let_binding v (fun x => e))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let'  x  ':='  v  'in' ']'  '/'  '[' e ']' ']'").

Notation "'Let' x ':' A ':=' v 'in' e" := (let_binding (v:A) (fun x:A => e))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let'  x  ':'  A  ':='  v  'in' ']'  '/'  '[' e ']' ']'").


Lemma let_binding_unfold : forall (A B:Type) (v:A) (K:A->B),
  let_binding v K = K v.
Proof. reflexivity. Qed.

Ltac let_get_fresh_binding_name K :=
  match K with (fun x => _) => let y := fresh x in y end.

(** [changes] is like [change] except that it does not silently
   fail to perform its task. Moreover, it does beta-unfolding *)

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" hyp(H) :=
  asserts_rewrite (E1 = E2) in H; [ reflexivity | ].
Tactic Notation "changes" constr(E1) "with" constr(E2) :=
  asserts_rewrite (E1 = E2); [ reflexivity | ].
Tactic Notation "changes" constr(E1) "with" constr(E2) "in" "*" :=
  asserts_rewrite (E1 = E2) in *; [ reflexivity | ].

Tactic Notation "let_simpl" "in" hyp(H) :=
  match type of H with context [ let_binding ?v ?K ] =>
     changes (let_binding v K) with (K v) in H
  end.

Tactic Notation "let_name" "in" hyp(H) :=
  match type of H with context [ let_binding ?v ?K ] =>
     let x := let_get_fresh_binding_name K in
     set_eq x: v in H;
     let_simpl in H
  end.

Tactic Notation "let_name" "in" hyp(H) "as" ident(x) :=
  match type of H with context [ let_binding ?v ?K ] =>
     set_eq x: v in H;
     let_simpl in H
  end.

Tactic Notation "let_simpl" :=
  match goal with
  | |- context [ let_binding ?v ?K ] =>
     changes (let_binding v K) with (K v)
  | H: context [ let_binding ?v ?K ] |- _ => let_simpl in H
  end.

Tactic Notation "let_name" :=
  match goal with
  | |- context [ let_binding ?v ?K ] =>
     let x := let_get_fresh_binding_name K in
     set_eq x: v;
     let_simpl
  | H: context [ let_binding ?v ?K ] |- _ => let_name in H
  end.

Tactic Notation "let_name" "as" ident(x) :=
  match goal with
  | |- context [ let_binding ?v ?K ] =>
     set_eq x: v;
     let_simpl
  | H: context [ let_binding ?v ?K ] |- _ => let_name in H as x
  end.

Definition let_binding_test_1 :
  (Let x := 3 in Let y := x + x in y + y) = 12.
Proof.
  dup 3.
  (* One can compute with Let *)
  reflexivity.
  (* One can inline Let step by step *)
  simpl. (* does nothing *)
  let_simpl.
  let_simpl.
  reflexivity.
  (* One can name the arguments of Let step by step *)
  let_name.
  let_name as z.
  subst x. subst z. reflexivity.
Qed.

Definition let_binding_test_2 :
  (Let x := 3 in Let y := x + x in y + y) = 12 -> True.
Proof.
  dup 2; intros H.
  (* One can inline Let step by step *)
  simpl in H. (* does nothing *)
  let_simpl in H.
  let_simpl in H.
  auto.
  (* One can name the arguments of Let step by step *)
  let_name in H.
  let_name in H as z.
  subst x. subst z. auto.
Qed.



(**************************************************************)
(** ** LATER: move to LibSet *)

Section Instances.
Variables (A:Type).

Global Instance incl_union_r_from_incl_union_l :
  Incl_union_l (T:=set A).
Admitted.
Global Instance set_incl_union_l :
  Incl_refl (T:=set A).
Admitted.
Global Instance set_incl_refl :
  Incl_trans (T:=set A).
Admitted.
End Instances.

Generalizable Variable T.

Lemma union_idem_r : forall A (E F:set A),
  E \u F \u F = E \u F.
Admitted.

Class In_incl `{BagIn A T} `{BagIncl T} :=
  { in_incl : forall E F, (forall x, x \in E -> x \in F) -> E \c F }.

Global Instance set_in_incl_inst : In_incl (A:=A) (T:=set A).
Proof. Admitted.


(**************************************************************)
(** ** LATER: move to LibList *)

Lemma list_case_last : forall A (l : list A),
  l = nil \/ exists x l', l = l'&x.
Proof. skip. Qed.

Lemma list_ind_last : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l & a)) ->
  forall l : list A, P l.
Proof.
  intros. induction_wf IH: (measure_wf (@LibList.length A)) l.
  skip.
Qed.

Lemma split_same_length : forall A B (l : list (A * B)) l1 l2,
  (l1, l2) = split l ->
  LibList.length l1 = LibList.length l2.
Proof.
  introv. gen l1 l2. induction l.
   introv E. inverts~ E.
   introv E. destruct a. simpl in E. sets_eq L: (split l).
    destruct L as (la&lb). inverts~ E.
    forwards~ E: IHl la lb.
    unfolds. do 2 rewrite fold_right_cons. unfolds in E. rewrite~ E.
Qed.

(* Stuff moved from JsSafety.v *)

Axiom last_eq_last_inv : forall A a1 a2 (l1 l2:list A),
  l1 & a1 = l2 & a2 -> l1 = l2 /\ a1 = a2.

Axiom case_last : forall A (l:list A),
  l = nil \/ exists x l', l = l' & x.

Axiom Forall_last_inv : forall A (P:A->Prop) l x,
  Forall P (l & x) ->
  P x /\ Forall P l.
(* todo: change hypotheses in forall_last *)


(**************************************************************)
(** ** LATER: move to LibReflect *)

Global Instance and_decidable :
  forall P1 P2, Decidable P1 -> Decidable P2 ->
  Decidable (P1 /\ P2).
Proof.
  introv D1 D2.
  applys decidable_make (decide P1 && decide P2).
  rewrite isTrue_and. repeat rewrite decide_spec. reflexivity.
Qed.


(**************************************************************)
(** ** LATER: move to LibFix *)

Require Import LibFix.

Definition FixFun4Mod B {IB:Inhab B} (E:binary B)
  A1 A2 A3 A4 (F:(A1->A2->A3->A4->B)->(A1->A2->A3->A4->B)) :=
  curry4 (FixFunMod E (fun f' => uncurry4 (F (curry4 f')))).

Definition FixFun4 B {IB:Inhab B} := FixFun4Mod eq.

Lemma FixFun4_fix_partial : forall A1 A2 A3 A4 (R:binary (A1*A2*A3*A4)) (P:A1->A2->A3->A4->Prop)
  B {IB:Inhab B} F (f:A1->A2->A3->A4->B),
  f = FixFun4 F -> wf R ->
  (forall x1 x2 x3 x4 f1 f2, P x1 x2 x3 x4 ->
    (forall y1 y2 y3 y4, P y1 y2 y3 y4 -> R (y1,y2,y3,y4) (x1,x2,x3,x4) -> f1 y1 y2 y3 y4 = f2 y1 y2 y3 y4) ->
     F f1 x1 x2 x3 x4 = F f2 x1 x2 x3 x4) ->
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 -> f x1 x2 x3 x4 = F f x1 x2 x3 x4).
Admitted.

Implicit Arguments FixFun4_fix_partial [A1 A2 A3 A4 B IB F f].

Definition FixFun5Mod B {IB:Inhab B} (E:binary B)
  A1 A2 A3 A4 A5 (F:(A1->A2->A3->A4->A5->B)->(A1->A2->A3->A4->A5->B)) :=
  curry5 (FixFunMod E (fun f' => uncurry5 (F (curry5 f')))).

Definition FixFun5 B {IB:Inhab B} := FixFun5Mod eq.

Lemma FixFun5_fix_partial : forall A1 A2 A3 A4 A5 (R:binary (A1*A2*A3*A4*A5)) (P:A1->A2->A3->A4->A5->Prop)
  B {IB:Inhab B} F (f:A1->A2->A3->A4->A5->B),
  f = FixFun5 F -> wf R ->
  (forall x1 x2 x3 x4 x5 f1 f2, P x1 x2 x3 x4 x5 ->
    (forall y1 y2 y3 y4 y5, P y1 y2 y3 y4 y5 -> R (y1,y2,y3,y4,y5) (x1,x2,x3,x4,x5) -> f1 y1 y2 y3 y4 y5 = f2 y1 y2 y3 y4 y5) ->
     F f1 x1 x2 x3 x4 x5 = F f2 x1 x2 x3 x4 x5) ->
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> f x1 x2 x3 x4 x5 = F f x1 x2 x3 x4 x5).
Admitted.

Implicit Arguments FixFun5_fix_partial [A1 A2 A3 A4 A5 B IB F f].


(**************************************************************)
(** ** move to LibList (or LibReflect?) *)

(* LibList.mem does not use `decide' but `isTrue' and is thus extracted
   classically. *)
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

Global Instance In_decidable : forall A : Set,
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

(**************************************************************)
(** ** move to LibList *)


Section LogicList.
Variables A B C D : Type.

(** Similar to [Forall2] except that it relates four lists *)

Inductive Forall4 (P : A -> B -> C -> D -> Prop)
  : list A -> list B -> list C -> list D -> Prop :=
  | Forall4_nil :
      Forall4 P nil nil nil nil
  | Forall4_cons : forall l1 l2 l3 l4 x1 x2 x3 x4,
      P x1 x2 x3 x4 -> Forall4 P l1 l2 l3 l4 ->
      Forall4 P (x1::l1) (x2::l2) (x3::l3) (x4::l4).
End LogicList.

Section ListProp.
Variables A B C D : Type.
Lemma Forall_trans : forall P Q : A -> Prop,
  (forall a, P a -> Q a) ->
  forall la, Forall P la ->
    Forall Q la.
Proof.
  introv I. intros.
  induction H.
    apply Forall_nil.
    apply~ Forall_cons.
Qed.

Lemma Forall4_trans : forall P Q : A -> B -> C -> D -> Prop,
  (forall a b c d, P a b c d -> Q a b c d) ->
  forall la lb lc ld, Forall4 P la lb lc ld ->
    Forall4 Q la lb lc ld.
Proof.
  introv I. intros.
  induction H.
    apply Forall4_nil.
    apply~ Forall4_cons.
Qed.

Lemma Forall3_trans : forall P Q : A -> B -> C -> Prop,
  (forall a b c, P a b c -> Q a b c) ->
  forall la lb lc, Forall3 P la lb lc->
    Forall3 Q la lb lc.
Proof.
  introv I. intros.
  induction H.
    apply Forall3_nil.
    apply~ Forall3_cons.
Qed.

(* FIXME: I do not know if those lemmas are really expressed in a
   natural and practical way. *)

Lemma Forall4_remove1 : forall P : B -> C -> D -> Prop,
  forall la lb lc ld,
  Forall4 (fun (_ : A) => P) la lb lc ld ->
  Forall3 P lb lc ld.
Proof.
  introv F4.
  induction F4.
    constructor.
    constructor~.
Qed.

Lemma Forall3_remove1 : forall P : B -> C -> Prop,
  forall la lb lc,
  Forall3 (fun (_ : A) => P) la lb lc ->
  Forall2 P lb lc.
Proof.
  introv F3.
  induction F3.
    constructor.
    constructor~.
Qed.

Lemma Forall3_permute12 : forall P : A -> B -> C -> Prop,
  forall la lb lc,
  Forall3 P la lb lc ->
  Forall3 (fun b a => P a b) lb la lc.
Proof.
  introv F3.
  induction F3.
    constructor.
    constructor~.
Qed.

Lemma Forall4_permute12 : forall P : A -> B -> C -> D -> Prop,
  forall la lb lc ld,
  Forall4 P la lb lc ld ->
  Forall4 (fun b a => P a b) lb la lc ld.
Proof.
  introv F4.
  induction F4.
    constructor.
    constructor~.
Qed.

Lemma Forall3_last_inv : forall (P : A -> B -> C -> Prop) l1 l2 l3 x1,
  Forall3 P (l1 & x1) l2 l3 ->
  exists r2 x2 r3 x3, l2 = r2 & x2 /\ l3 = r3 & x3
    /\ P x1 x2 x3 /\ Forall3 P l1 r2 r3.
Proof.
  introv H. sets_eq l': (l1&x1). gen l1 x1.
  induction H; intros; subst.
  false* nil_eq_last_inv.
  destruct l0; rew_app in EQl'; inverts EQl'.
    inverts H0. exists (@nil B) x2 (@nil C) x3. splits*. constructor.
    forwards~ (r2'&x2'&r3'&x3'&?&?&?): IHForall3. subst.
     exists (x2::r2') x2' (x3::r3') x3'. splits*. constructor*.
Qed.

End ListProp.


(**************************************************************)
(** ** move to LibReflect *)

Ltac case_if_on_tactic_core E Eq ::=
  match E with
  | @decide ?P ?M =>
      let Q := fresh in let Eq := fresh in
      forwards (Q&Eq): (@Decidable_dec P M);
      rewrite Eq in *; clear Eq; destruct Q
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in
           sets_eq <- X Eq: E;
           destruct X
    end
  end.


(**************************************************************)
(** ** LATER: move to LibReflect *)

Class Pickable (A : Type) (P : A -> Prop) := pickable_make {
  pick : A;
  pick_spec : (exists a, P a) -> P pick }.

Implicit Arguments pick [A [Pickable]].
Extraction Inline pick.


Class Pickable_option (A : Type) (P : A -> Prop) := pickable_option_make {
  pick_option : option A;
  pick_option_correct : forall a, pick_option = Some a -> P a;
  pick_option_defined : (exists a, P a) -> (exists a, pick_option = Some a) }.

Implicit Arguments pick_option [A [Pickable_option]].
Extraction Inline pick_option.

Global Instance Pickable_option_Pickable :
  forall (A : Type) (P : A -> Prop), Inhab A ->
  Pickable_option P -> Pickable P.
Proof.
  introv I [[pi|] C D].
   applys pickable_make pi. introv _. apply~ C.
   applys pickable_make arbitrary. introv E. forwards (a&N): D E. inverts N.
Qed.


Global Instance neg_decidable (P : Prop) :
  Decidable P -> Decidable (~ P).
Proof.
  introv [dec spec]. applys decidable_make (neg dec).
  rew_refl. rewrite~ spec.
Qed.

Global Instance or_decidable (P1 P2 : Prop) :
  Decidable P1 -> Decidable P2 ->
  Decidable (P1 \/ P2).
Proof.
  intros [d1 D1] [d2 D2].
  applys decidable_make (d1 || d2).
  rew_refl. subst~.
Qed.

Global Instance equal_pickable :
  forall (A : Type) (a : A),
  Pickable (eq a).
Proof.
  introv. applys pickable_make a.
  intro. reflexivity.
Qed.


(**************************************************************)
(** ** LATER: move to LibHeap *)

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
(** ** LATER: move to LibProd *)

(* Already there, but didn't work as instance... *)
Global Instance prod_inhab : forall A B : Type,
  Inhab A -> Inhab B ->
  Inhab (A * B).
Proof.
  introv IA IB.
  destruct IA. destruct inhabited as [a _].
  destruct IB. destruct inhabited as [b _].
  applys prove_Inhab (a, b).
Qed.


(**************************************************************)
(** ** LATER: move to LibInt *)

Global Instance le_int_decidable : forall i1 i2 : int, Decidable (i1 <= i2).
Admitted.

Global Instance ge_nat_decidable : forall n1 n2 : nat, Decidable (n1 >= n2).
Admitted.


(**************************************************************)
(** ** LATER: move to LibHeap *)

Global Instance heap_inhab : forall (K V : Type),
    Inhab (heap K V).
Proof.
  introv. apply (prove_Inhab empty).
Qed.


(**************************************************************)
(** ** LATER: move to LibLogic *)

Global Instance true_dec : Decidable True.
Proof. applys decidable_make true. rew_refl~. Qed.

Global Instance false_dec : Decidable False.
Proof. applys decidable_make false. rew_refl~. Qed.


(**************************************************************)

(** ** LATER: move to LibString *)

Parameter is_substring : string -> string -> Prop.

(* todo : implement a string comparison algorithm *)
Parameter is_substring_dec : forall s1 s2, Decidable (is_substring s1 s2).


(* todo: extract in a more clever way ! *)
Parameter int_of_char : Ascii.ascii -> int.

(**************************************************************)
(** ** LATER: move to LibReflect *)

Global Instance If_dec : forall P Q R,
  Decidable P -> Decidable Q -> Decidable R ->
  Decidable (If P then Q else R).
Proof.
  introv [p Hp] [q Hq] [r Hr]. applys decidable_make (if p then q else r).
  repeat cases_if~; false.
   rewrite~ isTrue_false in Hp; false.
   rewrite~ isTrue_true in Hp; false.
Qed.


(* The following lines are just a test with typeclasses. *) (* It's a `test', but it's on the path of the interpreter!  So please don't remove it. *)
(**************************************************************)
(** ** LATER: move to LibReflect *)

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

(**************************************************************)
(** ** LATER: move to LibHeap *)

Global Instance binds_functionnal : forall (H K : Type) (h : heap H K) k,
  Comparable H -> Inhab K ->
  FunctionalPred (binds h k).
Proof. introv C I. applys functionalpred_make. apply binds_func. Qed.
(* End of this little test. *)


(**************************************************************)
(** ** LATER: move to LibReflect *)

Global Instance eq_prop_dec : forall P Q : Prop,
  Decidable P -> Decidable Q ->
  Decidable (P = Q).
Proof.
  introv [p Hp] [q Hq]. applys decidable_make (decide (p = q)).
  skip. (* TODO *)
Qed.


(**************************************************************)
(** ** LATER: move to LibFunc (?) *)

Global Instance unary_op_inhab : forall P : Type,
  Inhab (P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.

Global Instance binary_op_inhab : forall P : Type,
  Inhab (P -> P -> P).
Proof. introv. apply prove_Inhab. introv. auto*. Qed.


(**************************************************************)
(** ** LATER: move to LibString *)

(* TODO:  To be moved on LibString in TLC *)
Definition string_sub s (n l : int) : string :=
  substring (abs n) (abs l) s.

(* todo: move *)
Axiom ascii_compare : Ascii.ascii -> Ascii.ascii -> bool.
Global Instance ascii_comparable : Comparable Ascii.ascii.
Proof. applys (comparable_beq ascii_compare). skip. Qed. 
Axiom int_lt_dec : forall k1 k2 : int, Decidable (k1 < k2).

(* todo: implement using lib *)
Parameter string_concat : string -> string -> string.


(**************************************************************)
(** ** LATER: move to LibOption *)

Definition morph_option {B C : Type} (c : C) (f : B -> C) (op : option B) : C :=
  match op with
  | None => c
  | Some b => f b
  end.

Definition unmonad_option {B : Type} (default : B) (op : option B) : B :=
  morph_option default id op.


(**************************************************************)
(** ** LATER: move to LibList *)

Fixpoint map_nth {A B : Type} (d : B) (f : A -> B) (i : nat) (s : list A) : B :=
  match i, s with
  | O, a :: _ => f a
  | S i', _ :: s' => map_nth d f i' s'
  | _, _ => d
  end.

Definition get_nth {A : Type} (d : A) (i : nat) (s : list A) : A :=
  map_nth (fun _ : unit => d) (fun (x : A) _ => x) i s tt.

Lemma get_nth_nil : forall (A : Type) (d : A) (i : nat),
  get_nth d i nil = d.
Proof. introv. destruct~ i. Qed.

Lemma get_nth_null : forall (A : Type) (d a : A) (s : list A),
  get_nth d 0 (a :: s) = a.
Proof. introv. reflexivity. Qed.

Lemma get_nth_cons : forall (A : Type) (i : nat) (d a : A) (s : list A),
  get_nth d (S i) (a :: s) = get_nth d i s.
Proof. introv. reflexivity. Qed.


(**************************************************************)
(** ** LATER: move to LibReflect *)

Global Instance istrue_dec : forall b : bool,
  Decidable (b).
Proof. introv. rewrite~ istrue_def. typeclass. Qed.


(**************************************************************)
(** ** LATER: move to LibList *)

Global Instance Forall_dec : forall (A : Type) (P : A -> Prop),
  (forall a : A, Decidable (P a)) -> forall l : list A,
  Decidable (Forall P l).
Proof.
  introv H; introv. applys decidable_make
    (fold_left (fun a b => and b (decide (P a))) true l).
  tests: (Forall P l).
   rewrite~ isTrue_true. fold_bool.
    induction~ C. simpl. cases_if~.
   rewrite~ isTrue_false. fold_bool.
    induction~ l.
     false C. constructor~.
     simpl. cases_if~.
      apply~ IHl. intro F; apply C. constructor~.
      clear C IHl. induction* l.
Qed.


(**************************************************************)
(** ** LATER: move to LibUnit *)

Global Instance unit_comparable : Comparable unit.
Proof.
  apply make_comparable. intros [x]. destruct x.
  rewrite* prop_eq_True_back. typeclass.
Qed.


(**************************************************************)
(** ** LATER: move to LibList *)

Definition hd_inhab {A : Type} `{Inhab A} (l : list A) : A :=
  match l with
  | nil => arbitrary
  | a :: l' => a
  end.

Global Instance eq_nil_dec : forall (A : Type) (l : list A),
  Decidable (l = nil).
Proof.
   introv. destruct~ l.
    rewrite~ prop_eq_True_back. typeclass.
    rewrite~ prop_eq_False_back.
     typeclass.
     discriminate.
Qed.


(**************************************************************)
(** ** LATER: move to LibProd *)

Definition prod_compare {A B : Type} `{Comparable A} `{Comparable B} (x y : A * B) :=
  let (x1, x2) := x in let (y1, y2) := y in
  decide (x1 = y1 /\ x2 = y2).

Global Instance prod_comparable : forall A B : Type,
  Comparable A -> Comparable B -> Comparable (A * B).
Proof.
  introv CA CB. applys comparable_beq (@prod_compare A B _ _). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H; inverts~ H;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** LATER: move to LibFset *)

Lemma subset_inter_weak_l : forall {A : Type} (E F : fset A),
  FsetImpl.subset (FsetImpl.inter E F) E.
Proof. intros_all. rewrite FsetImpl.in_inter in H. auto*. Qed.

Lemma subset_inter_weak_r : forall {A : Type} (E F : fset A),
  FsetImpl.subset (FsetImpl.inter E F) F.
Proof. intros_all. rewrite FsetImpl.in_inter in H. auto*. Qed.



(**************************************************************)
(** ** Do not move in TLC *)

Notation "'if' b 'then' v1 'else' v2" :=
  (if (b : bool) then v1 else v2)
  (at level 200, right associativity) : type_scope.


(**************************************************************)
(** ** LATER: move to LibHeap *)

Module HeapId (Export Heap : HeapSpec) : HeapSpec.
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

End HeapId.


(**************************************************************)
(** ** LATER: move to LibOption *)

Lemma option_map_some_back : forall (A B : Type) (f : A -> B) ao (b : B),
  option_map f ao = Some b ->
  exists a, ao = Some a /\ f a = b.
Proof. introv E. destruct~ ao. exists a. splits~. inverts~ E. inverts E. Qed.

Lemma option_map_some_forw : forall (A B : Type) (f : A -> B) ao (a : A) (b : B),
  ao = Some a ->
  f a = b ->
  option_map f ao = Some b.
Proof. introv E1 E2. substs. fequals. Qed.

Lemma option_apply_some_back : forall (A B : Type) (f : A -> option B) ao (b : B),
                                 LibOption.apply f ao = Some b ->
                                 exists a, ao = Some a /\ f a = Some b.
Proof.  introv E. destruct~ ao. exists a. splits~. inverts~ E. Qed.

Lemma option_apply_some_forw : forall (A B : Type) (f : A -> option B) ao (a:A) (b:B),
  ao = Some a ->
  f a = Some b ->
  LibOption.apply f ao = Some b.
Proof. introv E1 E2. substs. unfold apply. apply E2. Qed.


(**************************************************************)
(** ** LATER: move to LibList *)


(** [list_get_last ls] returns [None] if the list given is empty
    or [Some (ls',x)] where [ls=ls'++x::nil] otherwise. *)

Fixpoint lib_get_last (A:Type) (ls:list A) : option (list A * A) :=
  match ls with
  | nil => None
  | a::ls' =>
    match ls' with
    | nil => Some (nil,a)
    | _ => option_map (fun p => let '(ls',x) := p in (a::ls',x)) (lib_get_last ls')
    end
  end.

Lemma lib_get_last_spec : forall (A:Type) (ls:list A),
  match lib_get_last ls with
  | None => (ls = nil)
  | Some (ls',x) => (ls = LibList.append ls' (x::nil))
  end.
Proof.
  intros. induction ls; simpl.
  auto.
  destruct ls as [|b ls].
    rew_list*.
    destruct (lib_get_last (b::ls)) as [(?&?)|]; simpls.
      rew_list*. congruence.
      congruence.
Qed.

Lemma lib_get_last_nil : forall (A:Type),
  lib_get_last (@nil A) = None.
Proof. auto. Qed.

Lemma lib_get_last_cons : forall (A:Type) ls,
  ls <> nil -> exists (x:A) (ls':list A),
     lib_get_last ls = Some (ls',x) 
  /\ ls = LibList.append ls' (x::nil).
Proof. 
  intros. lets M: (lib_get_last_spec ls).
  destruct (lib_get_last ls) as [(ls'&x)|]. 
    subst. exists* x ls'.
    false.
Qed.

Lemma In_filter : forall (A:Type) p (a : A) l,
  In a (LibList.filter p l) = (In a l /\ p a).
Proof.
  introv. gen a. induction l; extens; iff H; simpls*.
   rewrite filter_cons in H. cases_if.
    inverts H as [IH IL].
     auto*.
     rewrite* IHl in H.
    rewrite* IHl in H.
   unfold filter. simpl. cases_if; destruct H as [[?|I] P]; tryfalse.
    substs. left~.
    right~. rewrite* IHl.
    fold (filter p l). rewrite* IHl.
Qed.

Lemma In_nil : forall (A:Type) l,
  (forall a:A, ~ In a l) = (l = nil).
Proof.
  introv. extens. iff N.
   destruct~ l. false (N a). left~.
   subst. apply in_nil.
Qed.

Lemma Forall_impl : forall A P (l : list A),
  Forall P l = (forall a, In a l -> P a).
Proof.
  introv. induction l; extens; (iff F; [introv I|]); tryfalse.
   apply Forall_nil.
   inverts F as FH FL. inverts~ I. rewrite* IHl in FL.
   apply Forall_cons.
    apply F. left~.
    rewrite IHl. introv I. apply F. right~.
Qed.


