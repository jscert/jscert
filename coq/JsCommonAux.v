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
Implicit Type ty : type.

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

Global Instance same_value_dec : forall v1 v2,
  Decidable (same_value v1 v2).
Proof.
  introv. unfold same_value. case_if. typeclass.
  destruct (type_of v1) eqn:H1; repeat cases_if; try typeclass.
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
    ((rewrite~ prop_eq_True_back; apply true_decidable) ||
      (rewrite~ prop_eq_False_back; [apply false_decidable | discriminate])).
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
  introv. apply not_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_accessor_dec : forall Desc,
  Decidable (descriptor_is_accessor Desc).
Proof.
  introv. apply not_decidable.
  apply and_decidable; typeclass.
Qed.

Global Instance descriptor_is_generic_dec : forall Desc,
  Decidable (descriptor_is_generic Desc).
Proof. typeclass. Qed.

Global Instance prepost_unary_op_dec : forall op,
  Decidable (prepost_unary_op op).
Proof.
  introv. destruct op;
    solve [ applys decidable_make true; fold_bool; fold_prop;
            do 2 eexists; constructors ]
    || solve [ applys decidable_make false; fold_bool; fold_prop;
               introv (f&b&H); inverts H ].
Qed.

Global Instance attributes_is_data_dec : forall A,
  Decidable (attributes_is_data A).
Proof. intro A. destruct A; typeclass. Qed.


Definition run_object_heap_map_properties S l F : option state :=
  LibOption.map
    (fun O => object_write S l (object_map_properties O F))
    (pick_option (object_binds S l)).

Global Instance object_heap_map_properties_pickable_option : forall S l F,
  Pickable_option (object_heap_map_properties S l F).
Proof.
  introv. unfold object_heap_map_properties.
  applys pickable_option_make (run_object_heap_map_properties S l F).
   introv E. forwards (O&P&E'): map_on_inv (rm E).
    exists O. splits~. apply~ @pick_option_correct.
  introv [S' [O [B E]]]. exists S'. unfolds.
   forwards Ex: ex_intro B. forwards~ (?&P): @pick_option_defined Ex.
   rewrite P. simpl. fequals. forwards C: @pick_option_correct P.
   forwards: @Heap_binds_func B C. typeclass. substs~.
Qed.

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

Definition run_function_get_error_case S x v : bool :=
  match v with
  | value_prim w => false
  | value_object l => 
    andb (ifb (x = "caller") then true else false)
    (option_case false (fun O => 
       option_case false (fun bd => 
          funcbody_is_strict bd) (object_code_ O)) (pick_option (object_binds S l)))
    
  end.

Global Instance spec_function_get_error_case_dec : forall S x v,
  Decidable (spec_function_get_error_case S x v).
Proof. 
  introv. applys decidable_make (run_function_get_error_case S x v).
  destruct v; simpl.
    fold_bool. rewrite is_False with (P := spec_function_get_error_case _ _ _).
      rewrite* isTrue_false.   
      
      intro A. unfold spec_function_get_error_case in A.
      destruct A as [xcaller [l [bd [B C]]]]. invert B.
 
    case_if; simpl.
    tests : (spec_function_get_error_case S x o).

    rewrite~ isTrue_true. lets (c&O&fb&E&H): (rm C).
    unfold object_method in H. 
    destruct H as [[O0 [H1 H2]] H3].
    forwards Ex: ex_intro H1. forwards (O1&H4): @pick_option_defined Ex.
    inversion E. 
    rewrite H4. simpl. asserts: (O0 = O1).
      forwards: @pick_option_correct H4. 
      applys Heap_binds_func H1 H. typeclass.
      substs. rewrite~ H2.

    rewrite~ isTrue_false. unfold spec_function_get_error_case in C. 
    rew_logic in C.
    destruct C as [C1 | C2]. contradiction.
    unfold object_method in C2.
    sets_eq <- Ob PS: (pick_option (object_binds S o)).
    destruct~ Ob as [o'|]. forwards B: @pick_option_correct PS. simpl.
    sets_eq <- Oc CD: (object_code_ o'). destruct~ Oc.

    assert (exists b, funcbody_is_strict f = b) as H.
    exists (funcbody_is_strict f). trivial.
    destruct H as [b H2].
    destruct b.

    false (C2 o). exists* f.
    apply H2.

    rewrite~ isTrue_false. introv H. 
    unfold spec_function_get_error_case in H.
    destruct H. contradiction.    
Qed.

(** Decidable instance for [is_callable] *)

Definition run_callable S v : option (option call) :=
  match v with
  | value_prim w => Some None
  | value_object l =>
    option_case None (fun O => Some (object_call_ O)) (pick_option (object_binds S l))
  end.

Global Instance is_callable_dec : forall S v,
  Decidable (is_callable S v).
Proof.
  introv. applys decidable_make
    (option_case false (option_case false (fun _ => true)) (run_callable S v)).
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
     sets_eq <- Ob PS: (pick_option (object_binds S o)).
     destruct~ Ob as [o'|]. forwards B: @pick_option_correct PS. simpl.
     sets_eq <- Oc CD: (object_call_ o'). destruct~ Oc. false (C c). exists* o'.
Qed.

Global Instance object_properties_keys_as_list_pickable_option : forall S l,
  Pickable_option (object_properties_keys_as_list S l).
Proof.
  introv. applys pickable_option_make
    (LibOption.map (fun props =>
      LibList.map fst (Heap.to_list props))
    (LibOption.map object_properties_ (pick_option (object_binds S l)))).
   introv EQ. forwards (P&EQP&EQM): map_inv (rm EQ).
    forwards (o&EQo&EQB): map_inv (rm EQP).
    forwards OB: @pick_option_correct (rm EQo).
    exists P. splits.
     exists* o.
     subst a. apply~ permut_refl.
   introv (xs&P&(O&OB&PO)&HLP).
    forwards (O'&EQO'): @pick_option_defined (ex_intro _ O OB). rewrite EQO'.
    asserts_rewrite (O' = O) in *.
      forwards OB': @pick_option_correct EQO'.
      forwards~: Heap_binds_func OB OB'. typeclass.
    simpl. rewrite PO.
    eexists; auto*.
Qed.

