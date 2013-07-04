Set Implicit Arguments.
Require Import Shared.
Require Export JsSyntax JsSyntaxAux JsPreliminary.


(**************************************************************)
(** ** Implicit Types *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
(*Implicit Type B : builtin.*)
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(**************************************************************)
(** ** Auxilary instances to define some comparison operators *)

Global Instance if_some_then_same_dec : forall (A : Type) F (x y : option A),
  (forall u v : A, Decidable (F u v)) ->
  Decidable (if_some_then_same F x y).
Proof.
  introv D.
  destruct x; destruct y; simpls~; typeclass.
Qed.

Lemma if_some_value_then_same_self : forall vo,
  if_some_value_then_same vo vo.
Proof.
  introv. unfolds. unfolds. destruct~ vo. reflexivity.
Qed.

Lemma if_some_bool_then_same_self : forall bo,
  if_some_bool_then_same bo bo.
Proof.
  introv. destruct bo; simpls~.
Qed.


(**************************************************************)
(** ** Type [attributes_data] *)

(** Boolean comparison *)

Definition attributes_data_compare Ad1 Ad2 :=
  match Ad1, Ad2 with
  | attributes_data_intro v1 w1 e1 c1, attributes_data_intro v2 w2 e2 c2 =>
    decide (v1 = v2 /\ w1 = w2 /\ e1 = e2 /\ c1 = c2)
  end.

(** Decidable comparison *)

Global Instance attributes_data_comparable : Comparable attributes_data.
Proof.
  applys (comparable_beq attributes_data_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H;
    [lets~ (H1&H2&H3&H4): (rm H) | inverts~ H]; congruence.
  (* Note that this is not the usual proof, which didn't worked there. -- Martin. *)
Qed.


(**************************************************************)
(** ** Type [attributes_accessor] *)

(** Boolean comparison *)

Definition attributes_accessor_compare Aa1 Aa2 :=
  match Aa1, Aa2 with
  | attributes_accessor_intro v1 w1 e1 c1, attributes_accessor_intro v2 w2 e2 c2 =>
    decide (v1 = v2 /\ w1 = w2 /\ e1 = e2 /\ c1 = c2)
  end.

(** Decidable comparison *)

Global Instance attributes_accessor_comparable : Comparable attributes_accessor.
Proof.
  applys (comparable_beq attributes_accessor_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H;
    [lets~ (H1&H2&H3&H4): (rm H) | inverts~ H]; congruence.
  (* Note that this is not the usual proof, which didn't worked there. -- Martin. *)
Qed.


(**************************************************************)
(** ** Type [attributes] *)

(** Boolean comparison *)

Definition attributes_compare A1 A2 :=
  match A1, A2 with
  | attributes_data_of Ad1, attributes_data_of Ad2 => decide (Ad1 = Ad2)
  | attributes_accessor_of Aa1, attributes_accessor_of Aa2 => decide (Aa1 = Aa2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance attributes_comparable : Comparable attributes.
Proof.
  applys (comparable_beq attributes_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [full_descriptor] *)

(** Inhabitants **)

Global Instance full_descriptor_inhab : Inhab full_descriptor.
Proof. apply (prove_Inhab full_descriptor_undef). Qed.

(** Boolean comparison *)

Definition full_descriptor_compare An1 An2 :=
  match An1, An2 with
  | full_descriptor_undef, full_descriptor_undef => true
  | full_descriptor_some A1, full_descriptor_some A2 => decide (A1 = A2)
  | _, _ => false
  end.

(** Decidable comparison *)

Global Instance full_descriptor_comparable : Comparable full_descriptor.
Proof.
  applys (comparable_beq full_descriptor_compare). intros x y.
  destruct x; destruct y; simpl; rew_refl; iff;
   tryfalse; auto; try congruence.
Qed.


(**************************************************************)
(** ** Type [ref_kind] *)

(** Inhabitants **)

Global Instance ref_kind_inhab : Inhab ref_kind.
Proof. apply (prove_Inhab ref_kind_null). Qed.

(** Decidable comparison *)

Global Instance ref_kind_comparable : Comparable ref_kind.
Proof.
  apply make_comparable. introv.
  destruct x; destruct y;
    ((rewrite~ prop_eq_True_back; apply true_dec) ||
      (rewrite~ prop_eq_False_back; [apply false_dec | discriminate])).
Qed.


(**************************************************************)
(** ** Some pickable instances *)

Global Instance object_binds_pickable_option : forall S l,
  Pickable_option (object_binds S l).
Proof.
  introv. unfolds object_binds.
  applys pickable_option_make (Heap.read_option (state_object_heap S) l).
   introv E. rewrite <- @Heap.binds_equiv_read_option in E. auto*.
   introv [a Ba]. exists a. rewrite <- @Heap.binds_equiv_read_option. auto*.
Qed.

Global Instance env_record_binds_pickable_option : forall S L,
  Pickable_option (env_record_binds S L).
Proof.
  introv. unfold env_record_binds.
  applys pickable_option_make (Heap.read_option (state_env_record_heap S) L).
   introv E. rewrite <- @Heap.binds_equiv_read_option in E. auto*.
   introv [a Ba]. exists a. rewrite <- @Heap.binds_equiv_read_option. auto*.
Qed.

Global Instance decl_env_record_pickable_option : forall Ed x,
  Pickable_option (Heap.binds Ed x).
Proof.
  introv. applys pickable_option_make (Heap.read_option Ed x).
   introv E. rewrite <- @Heap.binds_equiv_read_option in E. auto*.
   introv [a Ba]. exists a. rewrite <- @Heap.binds_equiv_read_option. auto*.
Qed.


(**************************************************************)
(** ** Proof of decidability properties *)

Global Instance descriptor_is_data_dec : forall Desc,
  Decidable (descriptor_is_data Desc).
Proof.
  introv. apply neg_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_accessor_dec : forall Desc,
  Decidable (descriptor_is_accessor Desc).
Proof.
  introv. apply neg_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_generic_dec : forall Desc,
  Decidable (descriptor_is_generic Desc).
Proof. typeclass. Qed.

Global Instance prepost_unary_op_dec : forall op,
  Decidable (prepost_unary_op op).
Proof. introv. destruct op; typeclass. Qed.

Global Instance attributes_is_data_dec : forall A,
  Decidable (attributes_is_data A).
Proof. intro A. destruct A; typeclass. Qed.


Definition run_object_heap_map_properties S l F : option state :=
  option_map
    (fun O => object_write S l (object_map_properties O F))
    (pick_option (object_binds S l)).

Global Instance object_heap_map_properties_pickable_option : forall S l F,
  Pickable_option (object_heap_map_properties S l F).
Proof.
  introv. unfold object_heap_map_properties.
  applys pickable_option_make (run_object_heap_map_properties S l F).
   introv E. forwards (O&P&E'): option_map_some_back (rm E).
    exists O. splits~. apply~ @pick_option_correct.
  introv [S' [O [B E]]]. exists S'. unfolds.
   forwards Ex: ex_intro B. forwards~ (?&P): @pick_option_defined Ex.
   applys option_map_some_forw P. forwards C: @pick_option_correct P.
   forwards: @Heap_binds_func B C. typeclass. substs~.
Qed.

(*
Lemma object_heap_map_is_a_function : forall S l F S' S'',
                                        object_heap_map_properties S l F S' ->
                                        object_heap_map_properties S l F S'' ->
                                        S'=S''.
Proof.
  introv. unfold object_heap_map_properties. unfold object_binds.
  unfold object_write.
  introv [O1 [P1a P1b]] [O2 [P2a P2b]].
  generalize (@Heap_binds_func _ _ _ _ _ O1 O2 P1a P2a).
  introv Eq. substs~.
Qed.
*)

(* Daniele: auxiliary lemma for proving make_delete_event_is_a_function. 
   TODO: I guess style is not the best. *)

(*
Lemma search_proto_chain_is_a_function : forall S l x res res',  
                                           search_proto_chain S l x res ->
                                           search_proto_chain S l x res' ->
                                           res = res'.
Proof.
  intros S l x res res' H1 H2. 
  induction H1. 
    (* Base case: found *)
    destruct H2. 
      (* found *)
      auto. 
      (* not found *)
      false. 
      (* Inductive *)
      false.
    (* Base case: not found *)
    destruct H2. 
      (* found *)
      false. 
      (* not found *)
      auto.
      (* inductive *)
      destruct H2. destruct H0. destruct H0. destruct H2.
       unfold object_binds in H2, H0. forwards: Heap_binds_func H0 H2.
          typeclass.
       false.
    (* Inductive case *)
    destruct H2.
      (* found *)
      false.
      (* not found *)      
      destruct H0. destruct H3. destruct H0. destruct H3.
      unfold object_binds in H0, H3. forwards: Heap_binds_func H0 H3.
        typeclass.
        subst.
        false.
      (* inductive *)
      destruct H0. destruct H3. destruct H0. destruct H3.
      unfold object_binds in H0, H3. forwards: Heap_binds_func H0 H3.
        typeclass.
        subst.
        rewrite H6 in H5. inverts H5. apply IHsearch_proto_chain. auto.
Qed.
*)

(*
Lemma make_delete_event_is_a_function : forall S l x ev ev',
                                          make_delete_event S l x ev ->
                                          make_delete_event S l x ev' ->
                                          ev=ev'.
Proof.
  intros S l x ev ev' H1 H2. 
  destruct H1 as [S l x res ev P1 E1].
  destruct H2 as [S' l' x' res' ev' P2 E2]. 
  forwards: search_proto_chain_is_a_function P1 P2.
  subst. trivial.
Qed.
*)

(* Daniele: remove
Fixpoint run_search_proto_chain S l x : option object_loc := 
  match (decide (object_has_property S l x)) with 
    | true => Some l
    | false => match (pick_option (object_proto S l)) with 
      | Some prim_null => None
      | Some (value_object l') => run_search_proto_chain S l' x
      | _ => None
    end
end.
*) 

(*
Global Instance make_delete_event_pickable_option : forall S l x,
  Pickable_option (make_delete_event S l x).
Proof.
  Admitted.
*)


(* Daniele: remove
Definition run_object_rem_property S l x : option state :=
  LibOption.apply
    (fun S' => option_map (state_with_new_event S')
                          (pick_option (make_delete_event S' l x)))
    (pick_option (object_heap_map_properties S l (fun P => Heap.rem P x))).
*)

(* Daniele: remove
Global Instance object_rem_property_pickable_option : forall S l x,
  Pickable_option (object_rem_property S l x).
Proof.

  introv. unfold object_rem_property.
  applys pickable_option_make (run_object_rem_property S l x).
   introv E. 
   forwards (S'&P&E'): option_apply_some_back (rm E).
   forwards (ev&A&B): option_map_some_back (rm E').
    exists S' ev. splits~. apply~ @pick_option_correct.
   apply~ @pick_option_correct.
  introv (S' & S'' & ev & P). destructs P. exists S'. unfolds.
  forwards Ex: ex_intro H.
  forwards~ (?&P): @pick_option_defined Ex. applys option_apply_some_forw P.
  forwards~ (?&P2): @pick_option_correct P. destructs P2.
  destruct H. destructs H. 
  (* Now by H and H2 I should have x1=x2, and thence by H4 and H3 that S''=x0.  *)
  assert (x1=x2). unfolds object_binds.
   generalize (@Heap_binds_func _ _ _ _ _ x2 x1 H H2). auto.
                          
  assert (S''=x0). substs~.
  forwards ExMDE: ex_intro H0.
  forwards~ (?&MDE): @pick_option_defined (ExMDE). 
  assert (x3=ev).
   apply pick_option_correct in MDE.
   apply make_delete_event_is_a_function with S'' l x.
    apply MDE.
   apply H0.
  substs.
  applys option_map_some_forw.
   apply MDE.
  trivial.
Qed.
*)

Global Instance descriptor_contains_dec : forall Desc1 Desc2,
  Decidable (descriptor_contains Desc1 Desc2).
Proof.
  intros Desc1 Desc2. destruct Desc1; destruct Desc2.
  simpl. repeat apply and_decidable; try typeclass.
Qed.

Global Instance descriptor_enumerable_not_same_dec : forall A Desc,
   Decidable (descriptor_enumerable_not_same A Desc).
Proof.
  introv. unfolds descriptor_enumerable_not_same.
  destruct (descriptor_enumerable Desc); try typeclass.
Qed.

Global Instance descriptor_value_not_same_dec : forall Ad Desc,
   Decidable (descriptor_value_not_same Ad Desc).
Proof.
  introv. unfolds descriptor_value_not_same.
  destruct (descriptor_value Desc); try typeclass.
Qed.

Global Instance descriptor_get_not_same_dec : forall Aa Desc,
   Decidable (descriptor_get_not_same Aa Desc).
Proof.
  introv. unfolds descriptor_get_not_same.
  destruct (descriptor_get Desc); try typeclass.
Qed.

Global Instance descriptor_set_not_same_dec : forall Aa Desc,
   Decidable (descriptor_set_not_same Aa Desc).
Proof.
  introv. unfolds descriptor_set_not_same.
  destruct (descriptor_set Desc); try typeclass.
Qed.

Global Instance attributes_change_enumerable_on_non_configurable_dec : forall A Desc,
  Decidable (attributes_change_enumerable_on_non_configurable A Desc).
Proof. introv. apply and_decidable; try typeclass. Qed.

Global Instance attributes_change_data_on_non_configurable_dec : forall Ad Desc,
  Decidable (attributes_change_data_on_non_configurable Ad Desc).
Proof. introv. repeat apply and_decidable; try typeclass. Qed.

Global Instance attributes_change_accessor_on_non_configurable_dec : forall Aa Desc,
  Decidable (attributes_change_accessor_on_non_configurable Aa Desc).
Proof. introv. typeclass. Qed.

(** Decidable instance for [is_callable] *)

Definition run_callable S v : option (option call) :=
  match v with
  | value_prim w => Some None
  | value_object l =>
    morph_option None (fun O => Some (object_call_ O)) (pick_option (object_binds S l))
  end.

Global Instance is_callable_dec : forall S v,
  Decidable (is_callable S v).
Proof.
  introv. applys decidable_make
    (morph_option false (morph_option false (fun _ => true)) (run_callable S v)).
  destruct v; simpl.
   fold_bool. rewrite is_False with (P := is_callable _ _). rewrite* isTrue_false.
    intro A. do 2 inverts A as A.
   tests: (is_callable S o).
    rewrite~ isTrue_true. lets (B&O&Bo&E): (rm C).
     forwards Ex: ex_intro Bo. forwards (O'&H): @pick_option_defined Ex.
     rewrite H. simpl. asserts: (O = O').
      forwards: @pick_option_correct H. applys Heap_binds_func Bo H0. typeclass.
     substs. rewrite~ E.
    rewrite~ isTrue_false. unfold is_callable in C. rew_logic in C. simpls.
     unfold object_call in C. sets_eq <- Ob PS: (pick_option (object_binds S o)).
     destruct~ Ob as [o'|]. forwards B: @pick_option_correct PS. simpl.
     sets_eq <- Oc CD: (object_call_ o'). destruct~ Oc. false (C c). exists* o'.
Qed.

Global Instance object_properties_keys_as_list_pickable_option : forall S l,
  Pickable_option (object_properties_keys_as_list S l).
Proof.
  introv. applys pickable_option_make
    (option_map (fun props =>
      LibList.map fst (Heap.to_list props))
    (option_map object_properties_ (pick_option (object_binds S l)))).
  skip. skip. (* Needs properties about [heap_keys_as_list]. *)
Qed.


