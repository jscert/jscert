Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSemanticsDefs. (* JsSemanticsAux *)


(**************************************************************)
(** ** Implicit Types *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type s : string.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type T : type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.

Implicit Type x : prop_name.
Implicit Type m : mutability.
Implicit Type A : prop_attributes.
Implicit Type An : prop_descriptor.
Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type D : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.


(**************************************************************)
(** ** Some functions to be implemented (or extracted differently). *)

Parameter JsNumber_to_int : JsNumber.number -> (* option? *) int.

Global Instance le_int_decidable : forall i1 i2, Decidable (i1 <= i2).
Admitted.


(**************************************************************)
(** To be moved in TLC *)

Class Pickable (A : Type) (P : A -> Prop) := pickable_make {
  pick : A;
  pick_spec : (exists a, P a) -> P pick }.

Implicit Arguments pick [A [Pickable]].
Extraction Inline pick.


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

Global Instance binds_pickable : forall K V : Type,
  `{Comparable K} -> `{Inhab V} ->
  forall (h : heap K V) (v : K),
  Pickable (binds h v).
Proof.
  introv CK IV; introv. applys pickable_make (read h v).
  introv [a Ba].
  apply~ read_binds. applys @binds_indom Ba.
Qed.


(**************************************************************)
(** To be moved in JsSemanticsAux *)

Lemma prim_compare_correct : forall w1 w2,
  prim_compare w1 w2 = isTrue (w1 = w2).
Proof.
  extens.
  destruct w1; destruct w2; simpl; rew_refl;
   try solve [ iff M; tryfalse; auto; try congruence ].
Qed.

Lemma value_compare_correct : forall v1 v2,
  value_compare v1 v2 = isTrue (v1 = v2).
Proof.
  extens.
  destruct v1; destruct v2; simpl; rew_refl;
   try solve [ iff M; tryfalse; auto; try congruence ].
Qed.

Global Instance prim_comparable : Comparable prim.
Proof.
  apply make_comparable.
  introv. applys decidable_make (prim_compare x y).
  apply* prim_compare_correct.
Qed.

Global Instance value_comparable : Comparable value.
Proof.
  apply make_comparable.
  introv. applys decidable_make (value_compare x y).
  apply* value_compare_correct.
Qed.

Global Instance prod_inhab : forall A B : Type,
  Inhab A -> Inhab B ->
  Inhab (A * B).
Proof.
  introv IA IB.
  destruct IA. destruct inhabited as [a _].
  destruct IB. destruct inhabited as [b _].
  applys prove_Inhab (a, b).
Qed.

Global Instance sate_inhab : Inhab state.
Admitted.

Global Instance prop_descriptor_inhab : Inhab prop_descriptor.
Proof. apply (prove_Inhab prop_descriptor_undef). Qed.

Global Instance prop_descriptor_comparable : Comparable prop_descriptor.
Admitted.

Global Instance object_inhab : Inhab object.
Proof.
  apply prove_Inhab. apply object_create; try apply arbitrary.
  apply empty.
Qed.

Global Instance res_inhab : Inhab res.
Proof.
  destruct value_inhab. destruct inhabited as [r _].
  apply prove_Inhab. apply res_normal. apply~ ret_value.
Qed.

Definition mutability_compare m1 m2 : bool :=
  match m1, m2 with
  | mutability_uninitialized_immutable, mutability_uninitialized_immutable => true
  | mutability_immutable, mutability_immutable => true
  | mutability_nondeletable, mutability_nondeletable => true
  | mutability_deletable, mutability_deletable => true
  | _, _ => false
  end.

Global Instance mutability_comparable : Comparable mutability.
Proof.
  apply make_comparable. introv.
  applys decidable_make (mutability_compare x y).
  destruct x; destruct y; simpl; rew_refl;
    ((rewrite~ eqb_eq; fail) || (rewrite~ eqb_neq; discriminate)).
Qed.

Global Instance prop_attributes_contains_dec : forall oldpf newpf,
  Decidable (prop_attributes_contains oldpf newpf).
Proof.
  introv. destruct oldpf. destruct newpf. simpl.
  repeat apply and_decidable.
Admitted.

Global Instance change_enumerable_attributes_on_non_configurable_dec : forall oldpf newpf,
  Decidable (change_enumerable_attributes_on_non_configurable oldpf newpf).
Admitted.

Global Instance change_data_attributes_on_non_configurable_dec : forall oldpf newpf,
  Decidable (change_data_attributes_on_non_configurable oldpf newpf).
Admitted.

Global Instance change_accessor_on_non_configurable_dec : forall oldpf newpf,
  Decidable (change_accessor_on_non_configurable oldpf newpf).
Admitted.

Global Instance object_loc_comparable : Comparable object_loc.
Admitted.

Global Instance binds_exists_property_pickable :
  forall (A B : Type) (P : A -> Prop) (Q : A -> B -> Prop),
  `{Pickable P} -> `{forall a : A, Pickable (Q a)} ->
  Pickable (fun b : B => exists (a : A), P a /\ Q a b).
Admitted.

Lemma pi S l : Pickable (object_binds S l).
Proof.
  typeclass.
Qed.

Typeclasses Transparent object_binds.

Set Printing All.

Definition test1 S l := @pick object (object_binds S l) _.
Definition test2 S l := pick (object_proto S l).


(**************************************************************)
(** ** Some types used by the interpreter *)

Inductive out_interp :=
  | out_interp_normal : out -> out_interp
  | out_interp_stuck : out_interp
  | out_interp_bottom : out_interp.


Global Instance out_interp_inhab : Inhab out_interp.
Proof. applys prove_Inhab out_interp_stuck. Qed.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section SmallConversions.

Definition run_convert_number_to_bool (n : number) :=
  decide (n = JsNumber.zero \/ n = JsNumber.neg_zero \/ n = JsNumber.nan).

Definition run_convert_string_to_bool s :=
  decide (s = "").

Definition run_convert_number_to_integer (n : number) :=
  ifb n = JsNumber.nan then JsNumber.zero
  else (
    ifb n = JsNumber.zero \/
        n = JsNumber.neg_zero \/
        n = JsNumber.infinity \/ n = JsNumber.neg_infinity then n
     else JsNumber.mult (JsNumber.sign n)
            (JsNumber.floor (JsNumber.absolute n))
  ).

Definition run_convert_primitive_to_integer w :=
  run_convert_number_to_integer (convert_prim_to_number w).

Definition run_convert_prim_to_boolean w :=
  match w with
  | prim_undef => false
  | prim_null => false
  | prim_bool b => b
  | prim_number n => run_convert_number_to_bool n
  | prim_string s => run_convert_string_to_bool s
  end.

Definition run_convert_value_to_boolean v :=
  match v with
  | value_prim p => run_convert_prim_to_boolean p
  | value_object _ => true
  end.


Definition run_option_transfer {A : Type} `{Comparable A} (oldopt newopt : option A) :=
  ifb newopt <> None then newopt else oldopt.

Definition run_prop_attributes_transfer oldpf newpf := 
  match oldpf, newpf with 
  | prop_attributes_intro ov ow og os oe oc, 
    prop_attributes_intro nv nw ng ns ne nc =>
    prop_attributes_intro 
      (run_option_transfer ov nv)
      (run_option_transfer ow nw)
      (run_option_transfer og ng)
      (run_option_transfer os ns)
      (run_option_transfer oe ne)
      (run_option_transfer oc nc)
  end.

(* I've just copy pasted it from JsSemanticsDefs:  if we change the specification, this one should be changed too. *)
Definition run_object_get_own_property_builder A :=
  let if_data {X:Type} (m:option X) (d:X) := 
    ifb prop_attributes_is_data A then Some (unsome_default d m) else None in
  let if_accessor {X:Type} (m:option X) (d:X) := 
    ifb prop_attributes_is_accessor A then Some (unsome_default d m) else None in
  {| prop_attributes_value := if_data (prop_attributes_value A) undef;
     prop_attributes_writable := if_data (prop_attributes_writable A) false;
     prop_attributes_get := if_accessor (prop_attributes_get A) undef;
     prop_attributes_set := if_accessor (prop_attributes_set A) undef;
     prop_attributes_enumerable := Some (unsome_default false (prop_attributes_enumerable A));
     prop_attributes_configurable := Some (unsome_default false (prop_attributes_configurable A)) |}.

End SmallConversions.

Section InterpreterEliminations.

Definition out_ter_interp S re :=
  out_interp_normal (out_ter S re).

Definition morph_option {B C : Type} (c : C) (f : B -> C) (op : option B) : C :=
  match op with
  | None => c
  | Some b => f b
  end.

Definition if_success (o : out_interp) (k : state -> ret -> out_interp) : out_interp :=
  match o with
  | out_interp_normal (out_ter S0 (res_normal re)) => k S0 re
  | _ => o
  end.

Definition if_success_throw (o : out_interp) (k1 : state -> res -> out_interp) (k2 : state -> value -> out_interp) : out_interp :=
  match o with
  | out_interp_normal (out_ter S0 (res_normal re)) => k1 S0 re
  | out_interp_normal (out_ter S0 (res_throw v)) => k2 S0 v
  | _ => o
  end.

Definition if_success_bool (o : out_interp) (k1 k2 : state -> out_interp) : out_interp :=
  if_success o (fun S re =>
    match re with
    | prim_bool b =>
      (if b then k1 else k2) S
    | _ => out_interp_stuck
    end).

Definition if_defined {B : Type} (op : option B) (k : B -> out_interp) : out_interp :=
  match op with
  | None => out_interp_stuck
  | Some a => k a
  end.

Definition if_defined_else {B C : Type} (op : option B) (k : B -> C) (k' : True -> C) : C :=
  match op with
  | None => k' I
  | Some a => k a
  end.

Definition if_value_object (o : out_interp) (k : state -> object_loc -> out_interp) : out_interp :=
  match o with
  | out_interp_normal (out_ter S0 re) =>
    match re with
    | res_normal rt =>
      match rt with
      | ret_value (value_object l) => k S0 l
      | _ => out_interp_stuck
      end
    | _ => o
    end
  | o => o
  end.

End InterpreterEliminations.

Section LexicalEnvironments.

Definition run_call_type : Type := (* Type of run_call *)
  state -> execution_ctx -> value -> list value -> value -> out_interp.

Definition run_object_class S l : string :=
  object_class_ (read (state_object_heap S) l).

Definition run_object_proto S l : value :=
  object_proto_ (read (state_object_heap S) l).

Definition run_object_properties S l : object_properties_type :=
  object_properties_ (read (state_object_heap S) l).

Definition run_object_extensible S l : bool :=
  object_extensible_ (read (state_object_heap S) l).

Definition run_object_get_own_property_base P x : prop_descriptor :=
  match read_option P x with
  | None => prop_descriptor_undef
  | Some A => prop_descriptor_some (run_object_get_own_property_builder A)
  end.

Definition run_object_get_own_property_default S l x : prop_descriptor :=
  run_object_get_own_property_base (run_object_properties S l) x.

Definition run_object_prim_value S l : value :=
  match object_prim_value_ (read (state_object_heap S) l) with
  | Some v => v
  | None => arbitrary
  end.

Definition run_object_get_own_property S l x : prop_descriptor :=
  let sclass := run_object_class S l in
  let An := run_object_get_own_property_default S l x in
  ifb sclass = "String" then (
    ifb An = prop_descriptor_undef then An
    else let ix := run_convert_primitive_to_integer x in
    ifb prim_string x <> convert_prim_to_string (prim_number (JsNumber.absolute ix)) then
      prop_descriptor_undef
    else (
      match run_object_prim_value S l with
      | prim_string s =>
        let len : int := String.length s in
        let i := JsNumber_to_int ix in
        ifb len <= i then prop_descriptor_undef
        else let s' := string_sub s i 1 in
          prop_attributes_create_data s' false true false
      | _ => arbitrary
      end
    )
  ) else An.

Definition object_get_property_body run_object_get_property S v x : prop_descriptor :=
  match v with
  | value_prim w =>
    ifb v = null then prop_descriptor_undef
    else arbitrary
  | value_object l =>
    let An := run_object_get_own_property S l x in
    ifb An = prop_descriptor_undef then (
      let lproto := run_object_proto S l in
      run_object_get_property S lproto x
    ) else An
  end.

Definition run_object_get_property := FixFun3 object_get_property_body.

Definition env_record_lookup {B : Type} (d : B) S L (K : env_record -> B) : B :=
  match read_option (state_env_record_heap S) L with
  | Some er => K er
  | None => d
  end.

Definition object_has_prop S l x : bool :=
  let An := run_object_get_property S (value_object l) x in
  decide (An <> prop_descriptor_undef).

Definition env_record_has_binding S L x (strict : bool) : option bool :=
  env_record_lookup None S L (fun er =>
    match er with
    | env_record_decl D =>
      Some (decide (decl_env_record_indom D x))
    | env_record_object l pt =>
      Some (object_has_prop S l x)
    end).

Fixpoint lexical_env_get_identifier_ref S X x (strict : bool) : ref :=
  match X with
  | nil => ref_create_value undef x strict
  | L :: X' =>
    if env_record_has_binding S L x strict then
      ref_create_env_loc L x strict
    else lexical_env_get_identifier_ref S X' x strict
  end.

Definition object_get S v x : out_interp :=
  match run_object_get_property S v x with
  | prop_descriptor_undef => out_ter_interp S undef
  | prop_descriptor_some A =>
    ifb prop_attributes_is_data A then
      @morph_option value _ out_interp_stuck (out_ter_interp S) (prop_attributes_value A)
    else out_interp_stuck
  end.

Definition run_alloc_primitive_value S w : state * object_loc :=
  arbitrary (* TODO *).

Definition to_object S v : out_interp :=
  match v with
  | prim_null | prim_undef => out_interp_normal (out_type_error S)
  | value_prim w =>
    let (S', l) := run_alloc_primitive_value S w in
    out_ter_interp S' l
  | value_object l => out_ter_interp S l
  end.

Definition object_get_special S v x : out_interp :=
  if_value_object (to_object S v) (fun S' l =>
    object_get S' l x).

Definition env_record_get_binding_value S L x (strict : bool) : out_interp :=
  env_record_lookup out_interp_stuck S L (fun er =>
    match er with
    | env_record_decl D =>
      let (mu, v) := read D x in
      ifb mu = mutability_uninitialized_immutable then
        out_interp_normal (out_ref_error_or_undef S strict)
      else out_ter_interp S v
    | env_record_object l pt =>
      if object_has_prop S l x then
        object_get S l x
      else out_interp_normal (out_ref_error_or_undef S strict)
    end).

Definition object_can_put S l x : out_interp :=
  let An := run_object_get_own_property S l x in
  let oe := run_object_extensible S l in
  match An with
  | prop_descriptor_some A =>
    ifb prop_attributes_is_accessor A then
      out_ter_interp S (decide (prop_attributes_set A = Some undef) || decide (prop_attributes_set A = None))
    else ifb prop_attributes_is_data A then
      out_ter_interp S (morph_option undef prim_bool (prop_attributes_writable A))
    else out_interp_stuck
  | prop_descriptor_undef =>
    let lproto := run_object_proto S l in
    ifb lproto = null then out_ter_interp S oe
    else (
      let Anproto := run_object_get_property S lproto x in
      match Anproto with
      | prop_descriptor_undef => out_ter_interp S oe
      | prop_descriptor_some A =>
        ifb prop_attributes_is_accessor A then
          out_ter_interp S (decide (prop_attributes_set A = Some undef) || decide (prop_attributes_set A = None))
        else ifb prop_attributes_is_data A then
          out_ter_interp S (if oe then false else morph_option undef prim_bool (prop_attributes_writable A))
        else out_interp_stuck
      end
    )
  end.

Definition run_out_reject S (bthrow : bool) :=
  if bthrow then out_type_error S
  else out_ter S false.

Definition run_object_set_property S l x A : state :=
  arbitrary (* TODO *).

Definition object_define_own_prop S l x (newpf : prop_attributes) (throw : bool) : out_interp :=
  let oldpd := run_object_get_own_property S l x in
  let extensible := run_object_extensible S l in
  match oldpd with
  | prop_descriptor_undef =>
    if extensible then (
      let S' := run_object_set_property S l x
        (if decide (prop_attributes_is_generic newpf) || decide (prop_attributes_is_data newpf) then
          prop_attributes_convert_to_data newpf
        else prop_attributes_convert_to_accessor newpf) in
      out_ter_interp S' true
    ) else out_interp_normal (run_out_reject S throw)
  | prop_descriptor_some oldpf =>
    let fman S' :=
      let S'' := run_object_set_property S' l x (run_prop_attributes_transfer oldpf newpf) in
      out_ter_interp S'' true in
    if extensible then (
      ifb prop_attributes_contains oldpf newpf then
        out_ter_interp S true
      else ifb change_enumerable_attributes_on_non_configurable oldpf newpf then
        out_interp_normal (run_out_reject S throw)
      else ifb prop_attributes_is_generic newpf then (
        fman S
      ) else ifb decide (prop_attributes_is_data oldpf) <> decide (prop_attributes_is_data newpf) then (
       ifb prop_attributes_configurable oldpf = Some false then
         out_interp_normal (run_out_reject S throw)
       else let S' := run_object_set_property S l x
        (ifb prop_attributes_is_data oldpf then
          prop_attributes_convert_to_accessor oldpf
        else prop_attributes_convert_to_data oldpf) in
        fman S'
     ) else if decide (prop_attributes_is_data oldpf) && decide (prop_attributes_is_data newpf) then (
       if decide (prop_attributes_configurable oldpf = Some false) && decide (change_data_attributes_on_non_configurable oldpf newpf) then
         out_interp_normal (run_out_reject S throw)
       else fman S
     ) else if decide (prop_attributes_is_accessor oldpf) && decide (prop_attributes_is_accessor newpf) then
       ifb change_accessor_on_non_configurable oldpf newpf then
         out_interp_normal (run_out_reject S throw)
       else fman S
     else out_interp_stuck
    ) else out_interp_stuck
  end.

Definition object_put S l x v (throw : bool) : out_interp :=
  if_success_bool (object_can_put S l x) (fun S =>
    let AnOwn := run_object_get_own_property S l x in
    match AnOwn with
    | prop_descriptor_undef => out_interp_stuck
    | prop_descriptor_some AO =>
      ifb prop_attributes_is_data AO then
        object_define_own_prop S l x (prop_attributes_create_value v) throw
      else (
        let An := run_object_get_property S (value_object l) x in
        match An with
        | prop_descriptor_undef => out_interp_stuck
        | prop_descriptor_some A =>
          arbitrary (* TODO *)
        end
      )
    end) (fun S =>
      (* I don't understand why, but this is not accepted by Coq:  out_interp_normal (run_out_reject S throw) *)
      if throw then
        out_interp_normal (out_type_error S)
      else out_ter_interp S false).

Definition env_record_set_mutable_binding S L x v (strict : bool) : out_interp :=
  match read (state_env_record_heap S) L with
  | env_record_decl D =>
    let (mu, v) := read D x in
    ifb mutability_is_mutable mu then
      arbitrary (* TODO:  This expression should be correct once [heap_set_environment_decl] will be declared:  out_ter_interp (heap_set_environment_decl S L x mu v) prim_undef *)
    else if strict then
      out_interp_normal (out_type_error S)
    else out_ter_interp S prim_undef
  | env_record_object l pt =>
    object_put S l x v strict
  end.

Definition env_record_create_mutable_binding S L x (deletable_opt : option bool) : out_interp :=
  let deletable := unsome_default false deletable_opt in
  match read (state_env_record_heap S) L with
  | env_record_decl D =>
    ifb decl_env_record_indom D x then out_interp_stuck
    else
      let S' := arbitrary (* TODO:  heap_set_environment_decl S L x (mutability_of_bool deletable) undef *) in
      out_interp_normal (out_void S')
  | env_record_object l pt =>
    if object_has_prop S l x then out_interp_stuck
    else let An := prop_attributes_create_data undef true true deletable in
      object_define_own_prop S l x An throw_true
  end.

Definition env_record_create_set_mutable_binding S L x (deletable_opt : option bool) v (strict : bool) : out_interp :=
  if_success (env_record_create_mutable_binding S L x deletable_opt) (fun S re =>
    match re with
    | prim_undef => env_record_set_mutable_binding S L x v strict
    | _ => out_interp_stuck
    end).


Definition ref_get_value S (re : ret) : out_interp :=
  match re with
  | ret_value v => out_ter_interp S v
  | ret_ref r =>
    match ref_kind_of r with
    | ref_kind_null | ref_kind_undef => out_interp_normal (out_ref_error S)
    | ref_kind_primitive_base =>
      match ref_base r with
      | ref_base_type_value v =>
        object_get_special S v (ref_name r)
      | ref_base_type_env_loc L =>
        env_record_get_binding_value S L (ref_name r) (ref_strict r)
      end
    | ref_kind_object => out_interp_stuck
    | ref_kind_env_record =>
      match ref_base r with
      | ref_base_type_value v => out_interp_stuck
      | ref_base_type_env_loc L =>
        env_record_get_binding_value S L (ref_name r) (ref_strict r)
      end
    end
  end.
  
Definition if_success_value (o : out_interp) (k : state -> value -> out_interp) : out_interp :=
  if_success o (fun S1 re1 =>
    if_success (ref_get_value S1 re1) (fun S2 re2 =>
      match re2 with
      | ret_value v => k S2 v
      | _ => out_interp_normal (out_ref_error S1)
      end)).


Definition run_is_callable S v : option function_code :=
  match v with
  | value_prim w => None
  | value_object l =>
    object_call_ (read (state_object_heap S) l)
  end.

Definition to_default (call : run_call_type) C S l (gpref : preftype) : out_interp :=
  let lpref := other_preftypes gpref in
  let gmeth := method_of_preftype gpref in
  let sub1 x K :=
    if_success (object_get S l x) (fun S1 re1 =>
      match re1 with
      | ret_value lf =>
        match run_is_callable S lf with
        | Some fc =>
          if_success_value (call S C lf nil l) (fun S2 v =>
            match v with
            | value_prim w => out_ter_interp S w
            | value_object l => K True
            end)
        | None => K True
        end
      | ret_ref _ => out_interp_stuck
      end) in
  sub1 gmeth (fun _ =>
    let lmeth := method_of_preftype lpref in
    sub1 lmeth (fun _ =>
      out_interp_normal (out_type_error S)
    )).

Definition to_primitive (call : run_call_type) C S v (gpref : preftype) : out_interp :=
  match v with
  | value_prim w => out_ter_interp S w
  | value_object l => to_default call C S l gpref
  end.

Definition to_number (call : run_call_type) C S v : out_interp :=
  match v with
  | value_prim w => out_ter_interp S (prim_number (convert_prim_to_number w))
  | value_object l =>
    if_success (to_primitive call C S (value_object l) preftype_number) (fun S1 re1 =>
      match re1 with
      | value_prim w =>
        out_ter_interp S (prim_number (convert_prim_to_number w))
      | _ => out_interp_stuck
      end)
  end.

Definition to_integer (call : run_call_type) C S v : out_interp :=
  if_success (to_number call C S v) (fun S1 re1 =>
    match re1 with
    | prim_number m =>
      out_ter_interp S (prim_number (convert_number_to_integer m))
    | _ => out_interp_stuck
    end).

Definition to_string (call : run_call_type) C S v : out_interp :=
  match v with
  | value_prim w => out_ter_interp S (convert_prim_to_string w)
  | value_object l =>
    if_success (to_primitive call C S (value_object l) preftype_string) (fun S1 re1 => (* TODO:  Define an “if_success_primitive” *)
      match re1 with
      | value_prim w =>
        out_ter_interp S (convert_prim_to_string w)
      | _ => out_interp_stuck
      end)
  end.


End LexicalEnvironments.


Section IntermediaryFunctions.

(* (* TODO:  Clean all that. *)
Definition if_is_loc_value v (f : loc -> option value) :=
  match v with
  | value_loc l => f l
  | _ => None
  end.

Definition lazy_binary_op_comp (h0 : heap) op v :=
  match op with
  | binary_op_and =>
    match v with
    | value_bool false => Some v
    | _ => None
    end

  | binary_op_or =>
    match v with
    | value_bool true => Some v
    | _ => None
    end

  | _ => None
  end.

Definition binary_op_comp_body binary_op_comp b h v1 v2 :=
  match b with
  | binary_op_equal =>
    ifb basic_value v1 /\ basic_value v2 then
      Some (value_bool (value_compare v1 v2))
    else None
  | binary_op_add =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_add n1 n2))
    | value_string s1, value_string s2 => Some (value_string (s1 ++ s2))
    | _, _ => None (* Type coercions are not performed yet. *)
    end
  | binary_op_mult =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_mult n1 n2))
    | _, _ => None (* Type coercions are not performed yet. *)
    end
  | binary_op_div =>
    match v1, v2 with
    | value_number n1, value_number n2 => Some (value_number (number_div n1 n2))
    | _, _ => None (* Type coercions are not performed yet. *)
    end
  | binary_op_in =>
    match v1, v2 with
    | value_string f, value_loc l => Some (value_bool
      (neg (decide ((proto_comp h (field_normal f) l) = loc_null))))
    | _, _ => None
    end
  | binary_op_instanceof =>
    if_is_loc_value v1 (fun l1 =>
      ifb basic_value v2 then Some (value_bool false)
      else match v2 with
         | value_loc l2 =>
           ifb indom h l1 field_normal_prototype then
             if_is_loc_value (read h l1 field_normal_prototype) (fun l3 =>
               ifb indom h l2 field_proto then
                 if_is_loc_value (read h l2 field_proto) (fun l4 =>
                   ifb l3 = l4 then
                     Some (value_bool true)
                   else
                     binary_op_comp binary_op_instanceof h (value_loc l1) (value_loc l4)
                 )
               else None
             )
           else None
         | _ => None
         end)
  | binary_op_and =>
    match v1 with
      | value_bool true => Some v2
      | _ => None
    end
  | binary_op_or =>
    match v1 with
      | value_bool false => Some v2
      | _ => None
    end
  end.

Definition binary_op_comp := FixFun4 binary_op_comp_body.

Definition unary_op_comp u (h : heap) v :=
  match u with
  | unary_op_void => Some value_undef
  | unary_op_not =>
    match v with
    | value_bool b => Some (value_bool (neg b))
    | _ => None
    end
  | _ => None
  end.

Definition typeof_comp h v :=
  match v with
  | value_undef => Some "undefined"%string
  | value_bool b => Some "boolean"%string
  | value_number n => Some "number"%string
  | value_string f => Some "string"%string
  | value_scope s => None
  | value_body f e => None
  | value_loc l =>
    ifb indom h l field_body then Some "function"%string
    else Some "object"%string
  end.

Fixpoint arguments_comp (lx : list string) (lv : list value) : list (field * value) :=
  match lx with
  | nil => nil
  | x :: lx' =>
    match lv with
    | nil =>
      (field_normal x, value_undef) :: arguments_comp lx' nil
    | v :: lv' =>
      (field_normal x, v) :: arguments_comp lx' lv'
    end
  end.
*)


Fixpoint run_list_expr (run_expr : state -> execution_ctx -> expr -> out_interp)
  S1 C (vs : list value) (es : list expr)
  (k : state -> list value -> out_interp) : out_interp :=
  match es with
  | nil => k S1 (LibList.rev vs)
  | e :: es' =>
    if_success_value (run_expr S1 C e) (fun S2 v =>
      run_list_expr run_expr S2 C (v :: vs) es' k)
  end.

End IntermediaryFunctions.

Section Interpreter.

(**************************************************************)
(** ** Definition of the interpreter *)

Fixpoint run_expr (max_step : nat) S C e : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_prog' := run_prog max_step' in
    match e with

    | expr_literal i =>
      out_ter_interp S (convert_literal_to_prim i)

    | expr_variable name =>
      arbitrary
      (* TODO:  let l := scope_comp h0 name s in
        out_return h0 (ret_ref l name) *)

    | expr_binary_op e1 op e2 =>
      arbitrary
      (* TODO:
      if_success_value (run_expr' h0 s e1) (fun h1 v1 =>
        if_defined_else (lazy_binary_op_comp h1 op v1) (fun v =>
          out_return h1 v) (fun _ =>
        if_success_value (run_expr' h1 s e2) (fun h2 v2 =>
          if_defined h2 (binary_op_comp op h2 v1 v2) (fun v =>
            out_return h2 v))))
      *)

    | expr_unary_op op e =>
      arbitrary
      (* TODO:
      match op with

      | unary_op_typeof =>
        if_success (run_expr' h0 s e) (fun h1 r1 =>
         if_is_null_ref r1 (fun _ =>
           out_return h1 (value_string "undefined")
         ) (fun _ =>
          if_defined h1 (getvalue_comp h1 r1) (fun v1 =>
            if_defined h1 (typeof_comp h1 v1) (fun str =>
              out_return h1 (value_string str)))))

     | unary_op_pre_incr | unary_op_pre_decr | unary_op_post_incr | unary_op_post_decr =>
       if_success (run_expr' h0 s e) (fun h1 r1 =>
         if_is_ref h1 r1 (fun l f =>
           if_defined h1 (getvalue_comp h1 r1) (fun v =>
           if_defined h1 (binary_op_comp binary_op_add h0
               match op with
               | unary_op_pre_incr | unary_op_post_incr => (number_of_int 1)
               | unary_op_pre_decr | unary_op_post_decr => (number_of_int (-1)%Z)
               | _ => arbitrary
               end v) (fun va =>
             let vr := match op with
                       | unary_op_pre_incr | unary_op_pre_decr => va
                       | unary_op_post_incr | unary_op_post_decr => v
                       | _ => arbitrary
                       end in
             let h2 := update h1 l f va in
             out_return h2 vr))))

      | unary_op_delete =>
        if_success (run_expr' h0 s e) (fun h1 r =>
          ifb dont_delete r then (
            out_return h1 (value_bool false))
          else (
            let h2 := dealloc h1 r in
            out_return h2 (value_bool true)))

      | _ =>
        if_success_value (run_expr' h0 s e) (fun h1 v1 =>
          if_defined h1 (unary_op_comp op h1 v1) (fun v =>
            out_return h1 v))

      end
      *)

    | expr_object lxe =>
      arbitrary
      (* TODO:
      (* allocate new object *)
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let '(lx,le0) := LibList.split lxe in
      (* writing the fields *)
      run_list_expr' h1 s nil le0 (fun h2 lv2 =>
              let lfv := arguments_comp lx lv2 in
              let h3 := write_fields h2 l lfv in
              out_return h3 (value_loc l))
      *)

    | expr_member e1 f =>
      run_expr' S C (expr_access e1 (expr_literal (literal_string f)))

    | expr_access e1 e2 =>
      if_success (run_expr' S C e1) (fun S1 re1 =>
        arbitrary (* TODO
        if_not_eq loc_null h1 (getvalue_comp h1 r1) (fun l =>
          if_success (run_expr' h1 s e2) (fun h2 r2 =>
            if_is_string h2 (getvalue_comp h2 r2) (fun f =>
              out_return h2 (ret_ref l f))))*))

    | expr_assign e1 opo e2 =>
      if_success (run_expr' S C e1) (fun S1 re1 =>
        match opo with
        | None =>
          if_success (run_expr' S1 C e2) (fun S2 re2 =>
            arbitrary (* TODO *))
        | Some op =>
          arbitrary (* TODO *)
        end)

    | expr_function _ _ _ => arbitrary
    (* TODO
    | expr_function None f e =>
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let l' := fresh_for h1 in
      let h2 := alloc_fun h1 l' s f e l in
      out_return h2 (value_loc l')

    | expr_function (Some y) f e =>
      let l := fresh_for h0 in
      let h1 := alloc_obj h0 l loc_obj_proto in
      let l1 := fresh_for h1 in
      let h2 := alloc_obj h1 l1 loc_obj_proto in
      let l' := fresh_for h2 in
      let h3 := alloc_fun h2 l' (l1 :: s) f e l in
      let h4 := write h3 l1 (field_normal y) (value_loc l') in
      out_return h4 (value_loc l')*)

    | expr_call e1 le2 =>
      arbitrary
      (* TODO
      if_success (run_expr' h0 s e1) (fun h1 r1 =>
        if_eq loc_eval h1 (getvalue_comp h1 r1) (fun _ =>
          make_error h0 "Not_implemented"
        ) (fun l1 =>
          let l2 := get_this h1 r1 in
          if_binds_scope_body h1 l1 (fun s3 lx P3 =>
            let ys := defs_prog lx P3 in
            run_list_expr' h1 s nil le2 (fun h2 lv2 =>
              let l3 := fresh_for h2 in
              let h3 := alloc_obj h2 l3 loc_null in
              let h4 := write h3 l3 field_this l2 in
              let lfv := arguments_comp lx lv2 in
              let h5 := write_fields h4 l3 lfv in
              let h6 := write_fields h5 l3
                (LibList.map (fun y => (field_normal y, value_undef)) ys) in
              if_success_value (run_prog' h6 (l3 :: s3) P3) (fun h7 v3 =>
                out_return h7 v3)))))
      *)

    | expr_this =>
      out_ter_interp S (execution_ctx_this_binding C)

    | expr_new e1 le2 =>
      arbitrary
      (* TODO
      (* Evaluate constructor *)
      if_success (run_expr' h0 s e1) (fun h1 r1 =>
        if_not_eq loc_null h1 (getvalue_comp h1 r1) (fun l1 =>
          if_binds_scope_body h1 l1 (fun s3 lx P3 =>
            if_binds_field field_normal_prototype h1 l1 (fun v1 =>
              let l2 := obj_or_glob_of_value v1 in
              (* Evaluate parameters *)
              run_list_expr' h1 s nil le2 (fun h2 lv2 =>
                (* Init new object *)
                let l4 := fresh_for h2 in
                let h3 := alloc_obj h2 l4 l2 in
                (* Create activation record *)
                let l3 := fresh_for h3 in
                let ys := defs_prog lx P3 in
                let h4 := write h3 l3 field_proto (value_loc loc_null) in
                let h5 := write h4 l3 field_this (value_loc l4) in
                let lfv := arguments_comp lx lv2 in
                let h6 := write_fields h5 l3 lfv in
                let h7 := reserve_local_vars h6 l3 ys in
                (* Execute function (constructor) body *)
                if_success_value (run_prog' h7 (l3 :: s3) P3) (fun h8 v3 =>
                  let l := obj_of_value v3 l4 in
                  out_return h8 (value_loc l)))))))
      *)

    end
  end

with run_stat (max_step : nat) S C t : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_stat' := run_stat max_step' in
    let run_expr' := run_expr max_step' in
    match t with

    | stat_expr e =>
      run_expr' S C e

    | stat_skip =>
      out_ter_interp S undef

    | stat_var_decl x eo =>
      match eo with
      | None => out_ter_interp S undef
      | Some e =>
        if_success (run_expr' S C e) (fun S1 re1 =>
          out_ter_interp S1 undef)
      end

    | stat_with e1 t2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if_success (to_object S1 v1) (fun S2 re2 =>
          match re2 with
          | value_object l =>
            let lex := execution_ctx_lexical_env C in
            let (lex', S3) := lexical_env_alloc_object S2 lex l provide_this_true in
            let C' := execution_ctx_with_lex_this C lex' l in
            run_stat' S3 C' t2
          | _ => arbitrary (* TODO:  Reread *)
          end))

    | stat_seq t1 t2 =>
      if_success (run_stat' S C t1) (fun S1 re1 =>
        if_success (run_stat' S1 C t2) (fun S2 re2 =>
          out_ter_interp S2 re2))

    | stat_if e1 t2 to =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if (run_convert_value_to_boolean v1) then
          run_stat' S1 C t2
        else
          match to with
          | Some t3 =>
            run_stat' S1 C t3
          | None =>
            out_ter_interp S undef
          end)

    | stat_while e1 t2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if (run_convert_value_to_boolean v1) then
          if_success (run_stat' S1 C t2) (fun S2 re2 =>
            run_stat' S2 C (stat_while e1 t2))
        else
          out_ter_interp S1 undef)

    | stat_throw e =>
      if_success_value (run_expr' S C e) (fun S1 v1 =>
        out_ter_interp S (res_throw v1))

    | stat_try t1 t2o t3o =>
      let finally :=
        match t3o with
        | None => fun o => o
        | Some t3 => fun o =>
          match o with
          | out_interp_normal (out_ter S1 re) =>
            if_success (run_stat' S1 C t3) (fun S2 re' =>
              out_ter_interp S2 re)
          | _ => o
          end
        end
      in
      if_success_throw (run_stat' S C t1) (fun S1 re1 =>
        finally (out_ter_interp S1 re1)) (fun S1 v =>
        match t2o with
        | None => finally (out_ter_interp S1 (res_throw v))
        | Some (x, t2) =>
          let lex := execution_ctx_lexical_env C in
          let (lex', S') := lexical_env_alloc_decl S lex in
          match lex' with
          | L :: oldlex =>
            if_success (env_record_create_set_mutable_binding S L x None v throw_irrelevant) (fun S2 re2 =>
              match re2 with
              | prim_undef =>
                let C' := execution_ctx_with_lex C lex' in
                finally (run_stat' S2 C' t2)
              | _ => out_interp_stuck
              end)
          | nil => out_interp_stuck
          end
        end)

    | stat_return eo =>
      match eo with
      | None =>
        out_ter_interp S (res_return undef)
      | Some e =>
        if_success_value (run_expr' S C e) (fun S1 v1 =>
          out_ter_interp S (res_return v1))
      end

    | stat_break =>
      arbitrary (* TODO *)

    | stat_continue =>
      arbitrary (* TODO *)

    | stat_for_in e1 e2 s =>
      arbitrary (* TODO *)

    | stat_for_in_var x e1o e2 s =>
      arbitrary (* TODO *)

    end
  end

with run_prog (max_step : nat) S C p : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_prog' := run_prog max_step' in
    let run_stat' := run_stat max_step' in
    match p with

    | prog_stat t =>
      run_stat' S C t

    | prog_seq p1 p2 =>
      if_success (run_prog' S C p1) (fun S1 re1 =>
        if_success (run_prog' S1 C p2) (fun S2 re2 =>
          out_ter_interp S2 re2))

    | prog_function_decl f lx P =>
      arbitrary (* TODO *)

    end
  end

with run_call (max_step : nat) S C (f : value) (ls : list value) v : out_interp :=
  arbitrary (* TODO *).

End Interpreter.

