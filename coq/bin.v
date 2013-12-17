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


Ltac decompose_base X I :=
  gen ltac_mark; gen X; intros X;
  let Y := fresh in set (Y:=X); destruct X as I; rename Y into X;
  intro_until_mark.

Tactic Notation "decompose" ident(E) "as" simple_intropattern(I) :=
  decompose_base E I.


(**************************************************************)
(** **  *)

(* should follow from Incl order:
Section Instances.
Variables (A:Type).
Global Instance set_incl_union_l :
  Incl_refl (T:=set A).
Admitted.
Global Instance set_incl_refl :
  Incl_trans (T:=set A).
Admitted.
End Instances.
*)

(* not used:
Lemma union_idem_r : forall A (E F:set A),
  E \u F \u F = E \u F.
Admitted.
*)

(* not used:
Lemma subset_inter_weak_l : forall {A : Type} (E F : fset A),
  FsetImpl.subset (FsetImpl.inter E F) E.
Proof. intros_all. rewrite FsetImpl.in_inter in H. auto*. Qed.

Lemma subset_inter_weak_r : forall {A : Type} (E F : fset A),
  FsetImpl.subset (FsetImpl.inter E F) F.
Proof. intros_all. rewrite FsetImpl.in_inter in H. auto*. Qed.
*)


(**************************************************************)

(* MARTIN: check where it is used ? 
   it's not clear why we'd ever need to compare propositions...:
   *)
Global Instance eq_prop_decidable : forall (P Q : Prop),
  Decidable P -> Decidable Q ->
  Decidable (P = Q). 
Proof.
  introv [p Hp] [q Hq]. applys decidable_make (decide (p = q)).
  skip. (* TODO : complete proof *)
Qed.


Lemma option_apply_some_back : forall (A B : Type) (f : A -> option B) ao (b : B),
                                 LibOption.apply f ao = Some b ->
                                 exists a, ao = Some a /\ f a = Some b.
Proof.  introv E. destruct~ ao. exists a. splits~. inverts~ E. Qed.

Lemma option_apply_some_forw : forall (A B : Type) (f : A -> option B) ao (a:A) (b:B),
  ao = Some a ->
  f a = Some b ->
  LibOption.apply f ao = Some b.
Proof. introv E1 E2. substs. unfold apply. apply E2. Qed.



Definition hd_inhab {A : Type} `{Inhab A} (l : list A) : A :=
  match l with
  | nil => arbitrary
  | a :: l' => a
  end.

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

(** [list_get_last ls] returns [None] if the list given is empty
    or [Some (ls',x)] where [ls=ls'++x::nil] otherwise. *)

Fixpoint lib_get_last (A:Type) (ls:list A) : option (list A * A) :=
  match ls with
  | nil => None
  | a::ls' =>
    match ls' with
    | nil => Some (nil,a)
    | _ => LibOption.map (fun p => let '(ls',x) := p in (a::ls',x)) (lib_get_last ls')
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



(* MARTIN: is this used anywhere ? *)
Parameter is_substring : string -> string -> Prop.
Parameter is_substring_dec : forall s1 s2, Decidable (is_substring s1 s2).

Axiom int_lt_dec : forall k1 k2 : int, Decidable (k1 < k2).
Extract Constant int_lt_dec => "(<)".


(* MARTIN: does not seem to be used *)
Definition unmonad_option {B : Type} (default : B) (op : option B) : B :=
  option_case default id op.
