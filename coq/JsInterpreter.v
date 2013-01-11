Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSyntax JsSyntaxAux JsPreliminary JsPreliminaryAux.


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
Implicit Type T : type.

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

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(**************************************************************)
(** ** Some functions to be implemented (or extracted differently). *)

Parameter JsNumber_to_int : JsNumber.number -> (* option? *) int.


(**************************************************************)
(** ** Some types used by the interpreter *)

Inductive out_interp :=
  | out_interp_normal : out -> out_interp
  | out_interp_stuck : out_interp
  | out_interp_bottom : out_interp.

(* Coercion *)

Coercion out_interp_normal : out >-> out_interp.

(* Inhabited *)

Global Instance out_interp_inhab : Inhab out_interp.
Proof. applys prove_Inhab out_interp_stuck. Qed.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section InterpreterEliminations.

Definition morph_option {B C : Type} (c : C) (f : B -> C) (op : option B) : C :=
  match op with
  | None => c
  | Some b => f b
  end.

Definition extract_from_option {B : Type} `{Inhab B} :=
  morph_option arbitrary id.

Definition if_success (o : out_interp) (k : state -> ret_or_empty -> out_interp) : out_interp :=
  match o with
  | out_ter S0 (res_normal re) => k S0 re
  | _ => o
  end.

Definition if_success_throw (o : out_interp) (k1 : state -> res -> out_interp) (k2 : state -> value -> out_interp) : out_interp :=
  match o with
  | out_ter S0 (res_normal re) => k1 S0 re
  | out_ter S0 (res_throw v) => k2 S0 v
  | _ => o
  end.

Definition if_success_bool (o : out_interp) (k1 k2 : state -> out_interp) : out_interp :=
  if_success o (fun S re =>
    match re with
    | prim_bool b =>
      (if b then k1 else k2) S
    | _ => out_interp_stuck
    end).

Definition if_success_primitive (o : out_interp) (k : state -> prim -> out_interp) : out_interp :=
  if_success o (fun S re =>
    match re with
    | value_prim w =>
      k S w
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
  | out_ter S0 re =>
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

Definition prop_attributes_is_generic_or_data A :=
  prop_attributes_is_generic A \/ prop_attributes_is_data A.

Global Instance prop_attributes_is_generic_or_data_dec : forall A,
  Decidable (prop_attributes_is_generic_or_data A).
Proof.
  introv. apply or_decidable.
   apply and_decidable; apply neg_decidable;
     apply neg_decidable; apply and_decidable; typeclass.
  apply neg_decidable; apply and_decidable; typeclass.
Qed.

End InterpreterEliminations.

Section LexicalEnvironments.

Definition run_object_proto S l : value :=
  object_proto_ (pick (object_binds S l)).

Definition run_object_class S l : string :=
  object_class_ (pick (object_binds S l)).

Definition run_object_extensible S l : bool :=
  object_extensible_ (pick (object_binds S l)).

Definition run_object_prim_value S l : value :=
  extract_from_option (object_prim_value_ (pick (object_binds S l))).

Definition run_object_call S l : option function_code :=
  object_call_ (pick (object_binds S l)).

Definition run_object_has_instance S l : bool :=
  object_has_instance_ (pick (object_binds S l)).

Definition run_object_scope S l : option lexical_env :=
  object_scope_ (pick (object_binds S l)).

Definition run_object_formal_parameters S l : option (list string) :=
  object_formal_parameters_ (pick (object_binds S l)).

Definition run_object_properties S l : object_properties_type :=
  object_properties_ (pick (object_binds S l)).

Definition run_object_heap_set_properties S l P' : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_with_properties O P').

Definition run_object_heap_map_properties S l F : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_map_properties O F).

Global Instance object_heap_map_properties_pickable : forall S l F,
  Pickable (object_heap_map_properties S l F).
Proof.
  introv. applys pickable_make (run_object_heap_map_properties S l F).
  introv [a [O [B E]]]. exists O. splits~.
  unfolds run_object_heap_map_properties.
  skip. (* binds is a functionnal construction. *)
Qed.

Definition run_object_get_own_property_base P x : prop_descriptor :=
  match read_option P x with
  | None => prop_descriptor_undef
  | Some A => prop_descriptor_some (object_get_own_property_builder A)
  end.

Definition run_object_get_own_property_default S l x : prop_descriptor :=
  run_object_get_own_property_base (run_object_properties S l) x.

Definition run_object_get_own_property S l x : prop_descriptor :=
  let sclass := run_object_class S l in
  let An := run_object_get_own_property_default S l x in
  ifb sclass = "String" then (
    ifb An = prop_descriptor_undef then An
    else let ix := convert_primitive_to_integer x in
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
  | prop_descriptor_undef => out_ter S undef
  | prop_descriptor_some A =>
    ifb prop_attributes_is_data A then
      morph_option out_interp_stuck (out_ter S : value -> _) (prop_attributes_value A)
    else out_interp_stuck
  end.

Definition run_alloc_primitive_value S w : state * object_loc :=
  arbitrary (* TODO *).

Definition to_object S v : out_interp :=
  match v with
  | prim_null | prim_undef => out_type_error S
  | value_prim w =>
    let (S', l) := run_alloc_primitive_value S w in
    out_ter S' l
  | value_object l => out_ter S l
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
        out_ref_error_or_undef S strict
      else out_ter S v
    | env_record_object l pt =>
      if object_has_prop S l x then
        object_get S l x
      else out_ref_error_or_undef S strict
    end).

Definition object_can_put S l x : out_interp :=
  let An := run_object_get_own_property S l x in
  let oe := run_object_extensible S l in
  match An with
  | prop_descriptor_some A =>
    ifb prop_attributes_is_accessor A then
      out_ter S (decide (prop_attributes_set A = Some undef
        \/ prop_attributes_set A = None))
    else ifb prop_attributes_is_data A then
      out_ter S (morph_option undef prim_bool (prop_attributes_writable A))
    else out_interp_stuck
  | prop_descriptor_undef =>
    let lproto := run_object_proto S l in
    ifb lproto = null then out_ter S oe
    else (
      let Anproto := run_object_get_property S lproto x in
      match Anproto with
      | prop_descriptor_undef => out_ter S oe
      | prop_descriptor_some A =>
        ifb prop_attributes_is_accessor A then
          out_ter S (decide (prop_attributes_set A = Some undef \/ prop_attributes_set A = None))
        else ifb prop_attributes_is_data A then
          out_ter S (if oe then false else morph_option undef prim_bool (prop_attributes_writable A))
        else out_interp_stuck
      end
    )
  end.

Definition object_define_own_prop S l x (newpf : prop_attributes) (throw : bool) : out_interp :=
  let oldpd := run_object_get_own_property S l x in
  let extensible := run_object_extensible S l in
  match oldpd with
  | prop_descriptor_undef =>
    if extensible then (
      let S' := pick (object_set_property S l x
        (if @decide (prop_attributes_is_generic_or_data newpf)
          (prop_attributes_is_generic_or_data_dec newpf) then (* Why Coq is not able to infer this?!? *)
          prop_attributes_convert_to_data newpf
        else prop_attributes_convert_to_accessor newpf)) in
      out_ter S' true
    ) else out_reject S throw
  | prop_descriptor_some oldpf =>
    let fman S' :=
      let S'' := pick (object_set_property S' l x (prop_attributes_transfer oldpf newpf)) in
      out_ter S'' true in
    if extensible then (
      ifb prop_attributes_contains oldpf newpf then
        out_ter S true
      else ifb change_enumerable_attributes_on_non_configurable oldpf newpf then
        out_reject S throw
      else ifb prop_attributes_is_generic newpf then (
        fman S
      ) else ifb prop_attributes_is_data oldpf <> prop_attributes_is_data newpf then (
       ifb prop_attributes_configurable oldpf = Some false then
         out_reject S throw
       else let S' := pick (object_set_property S l x
        (ifb prop_attributes_is_data oldpf then
          prop_attributes_convert_to_accessor oldpf
        else prop_attributes_convert_to_data oldpf)) in
        fman S'
     ) else ifb prop_attributes_is_data oldpf /\ prop_attributes_is_data newpf then (
       ifb prop_attributes_configurable oldpf = Some false /\ change_data_attributes_on_non_configurable oldpf newpf then
         out_reject S throw
       else fman S
     ) else ifb prop_attributes_is_accessor oldpf /\ prop_attributes_is_accessor newpf then
       ifb change_accessor_on_non_configurable oldpf newpf then
         out_reject S throw
       else fman S
     else out_interp_stuck
    ) else out_interp_stuck
  end.

Definition run_prog_type : Type := (* The funcion taking this as an argument can call any arbitrary code *)
  state -> execution_ctx -> prog -> out_interp.

Definition execution_ctx_binding_instantiation S C (funco : option object_loc) (code : function_code) (args : list value) : out_interp :=
  let L := hd (execution_ctx_variable_env C) in
  (* let names_option := run_object_formal_parameters S func in
  let names := unsome_default nil names_option in *) (* TODO *)
  arbitrary (* TODO *).

Definition execution_ctx_function_call S C (K : state -> execution_ctx -> out_interp) (lf : object_loc) (this : value) (args : list value) :=
  let strict : bool := arbitrary (* TODO *) in
  if_success (if strict then out_ter S this
    else ifb this = null \/ this = undef then out_ter S builtin_global
    else ifb type_of this = type_object then out_ter S this
    else to_object S this) (fun S1 newthis =>
      let scope := extract_from_option (run_object_scope S1 lf) in
      let fc := extract_from_option (run_object_call S1 lf) in
      let (lex', S2) := lexical_env_alloc_decl S1 scope in
      let strict' := execution_ctx_strict C (* TODO *) in
      let C' := execution_ctx_intro_same lex' this strict' in
      if_success (execution_ctx_binding_instantiation S2 C' (Some lf) fc args) (fun S3 re =>
        K S3 C')).
      

Definition call (run : run_prog_type) S C (fc : function_code) (lfo : option object_loc) (vo : option value) (args : list value) : out_interp :=
  match fc with
  | function_code_code p =>
    let lf := extract_from_option lfo in
    let this := extract_from_option vo in
    arbitrary (* TODO *)
  | function_code_builtin id =>
    arbitrary (* TODO *)
  end.

Definition object_put (run : run_prog_type) S C l x v (throw : bool) : out_interp :=
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
          ifb prop_attributes_is_accessor A then (
            match extract_from_option (prop_attributes_set A) with
            | value_object fsetter =>
              let fc := extract_from_option (run_object_call S fsetter) in
              call run S C fc (Some fsetter) (Some (value_object l)) (v :: nil)
            | _ => out_interp_stuck
            end) else (
              let A' := prop_attributes_create_data v true true true in
              object_define_own_prop S l x A' throw
            )
        end
      )
    end) (fun S => out_reject S throw).

Definition env_record_set_mutable_binding (run : run_prog_type) S C L x v (strict : bool) : out_interp :=
  match pick (env_record_binds S L) with
  | env_record_decl D =>
    let (mu, v) := read D x in
    ifb mutability_is_mutable mu then
      arbitrary (* TODO:  This expression should be correct once [heap_set_environment_decl] will be declared:  out_ter (heap_set_environment_decl S L x mu v) prim_undef *)
    else if strict then
      out_type_error S
    else out_ter S prim_undef
  | env_record_object l pt =>
    object_put run S C l x v strict
  end.

Definition env_record_create_mutable_binding S L x (deletable_opt : option bool) : out_interp :=
  let deletable := unsome_default false deletable_opt in
  match pick (env_record_binds S L) with
  | env_record_decl D =>
    ifb decl_env_record_indom D x then out_interp_stuck
    else
      let S' := arbitrary (* TODO:  heap_set_environment_decl S L x (mutability_of_bool deletable) undef *) in
      out_void S'
  | env_record_object l pt =>
    if object_has_prop S l x then out_interp_stuck
    else let An := prop_attributes_create_data undef true true deletable in
      object_define_own_prop S l x An throw_true
  end.

Definition env_record_create_set_mutable_binding (run : run_prog_type) S C L x (deletable_opt : option bool) v (strict : bool) : out_interp :=
  if_success (env_record_create_mutable_binding S L x deletable_opt) (fun S re =>
    match re with
    | prim_undef =>
      env_record_set_mutable_binding run S C L x v strict
    | _ => out_interp_stuck
    end).


Definition ref_get_value S (re : ret) : out_interp :=
  match re with
  | ret_value v => out_ter S v
  | ret_ref r =>
    match ref_kind_of r with
    | ref_kind_null | ref_kind_undef => out_ref_error S
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
    match re1 with
    | ret_or_empty_ret rer1 =>
        if_success (ref_get_value S1 rer1) (fun S2 re2 =>
          match re2 with
          | ret_value v => k S2 v
          | _ => out_ref_error S1
          end)
    | _ => out_ref_error S1
    end).

Definition run_callable S v :=
  match v with
  | value_prim w => None
  | value_object l =>
    run_object_call S l
  end.

Global Instance callable_pickable : forall S v,
  Pickable (callable S v).
Proof.
  introv. applys pickable_make (run_callable S v).
  intros [a Ha]. destruct v; simpls~.
  skip. (* TODO *)
Qed.

Definition to_default (run : run_prog_type) S C l (prefo : option preftype) : out_interp :=
  let gpref := unsome_default preftype_number prefo in
  let lpref := other_preftypes gpref in
  let gmeth := method_of_preftype gpref in
  let sub x K :=
    if_success (object_get S l x) (fun S1 re1 =>
      match re1 with
      | ret_value (value_object lfo) =>
        let lf := value_object lfo in
        match pick (callable S lf) with
        | Some fc =>
          if_success_value (call run S C fc (Some lfo) (Some lf) nil) (fun S2 v =>
            match v with
            | value_prim w => out_ter S w
            | value_object l => K True
            end)
        | None => K True
        end
      | _ => out_interp_stuck
      end) in
  sub gmeth (fun _ =>
    let lmeth := method_of_preftype lpref in
    sub lmeth (fun _ => out_type_error S)).

Definition to_primitive (run : run_prog_type) S C v (prefo : option preftype) : out_interp :=
  match v with
  | value_prim w => out_ter S w
  | value_object l => to_default run S C l prefo
  end.

Definition to_number (run : run_prog_type) S C v : out_interp :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_number w)
  | value_object l =>
    if_success_primitive (to_primitive run S C (value_object l) (Some preftype_number)) (fun S1 w =>
      out_ter S (convert_prim_to_number w))
  end.

Definition to_integer (run : run_prog_type) S C v : out_interp :=
  if_success (to_number run S C v) (fun S1 re1 =>
    match re1 with
    | prim_number n =>
      out_ter S (convert_number_to_integer n)
    | _ => out_interp_stuck
    end).

Definition to_string (run : run_prog_type) S C v : out_interp :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_string w)
  | value_object l =>
    if_success_primitive (to_primitive run S C (value_object l) (Some preftype_string)) (fun S1 w =>
      out_ter S (convert_prim_to_string w))
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
      out_ter S (convert_literal_to_prim i)

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
      out_ter S (execution_ctx_this_binding C)

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

    | expr_conditional e1 e2 e3 =>
      arbitrary (* TODO *)

    end
  end

with run_stat (max_step : nat) S C t : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_stat' := run_stat max_step' in
    let run_expr' := run_expr max_step' in
    let run_prog' := run_prog max_step' in
    match t with

    | stat_expr e =>
      run_expr' S C e

    | stat_skip =>
      out_ter S ret_empty

    | stat_var_decl x eo =>
      match eo with
      | None => out_ter S undef
      | Some e =>
        if_success (run_expr' S C e) (fun S1 re1 =>
          out_ter S1 undef)
      end

    | stat_seq t1 t2 =>
      if_success (run_stat' S C t1) (fun S1 re1 =>
        if_success (run_stat' S1 C t2) (fun S2 re2 =>
          out_ter S2
            match re2 with
            | ret_empty => re1
            | _ => re2
            end))

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

    | stat_if e1 t2 to =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if (convert_value_to_boolean v1) then
          run_stat' S1 C t2
        else
          match to with
          | Some t3 =>
            run_stat' S1 C t3
          | None =>
            out_ter S undef
          end)

    | stat_while e1 t2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if (convert_value_to_boolean v1) then
          if_success (run_stat' S1 C t2) (fun S2 re2 =>
            run_stat' S2 C (stat_while e1 t2))
        else
          out_ter S1 undef)

    | stat_throw e =>
      if_success_value (run_expr' S C e) (fun S1 v1 =>
        out_ter S (res_throw v1))

    | stat_try t1 t2o t3o =>
      let finally : out_interp -> out_interp :=
        match t3o with
        | None => fun o => o
        | Some t3 => fun o =>
          match o with
          | out_ter S1 re =>
            if_success (run_stat' S1 C t3) (fun S2 re' =>
              out_ter S2 re)
          | _ => o
          end
        end
      in
      if_success_throw (run_stat' S C t1) (fun S1 re1 =>
        finally (out_ter S1 re1)) (fun S1 v =>
        match t2o with
        | None => finally (out_ter S1 (res_throw v))
        | Some (x, t2) =>
          let lex := execution_ctx_lexical_env C in
          let (lex', S') := lexical_env_alloc_decl S lex in
          match lex' with
          | L :: oldlex =>
            if_success
            (env_record_create_set_mutable_binding run_prog' S C L x None v throw_irrelevant)
            (fun S2 re2 =>
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
        out_ter S (res_return undef)
      | Some e =>
        if_success_value (run_expr' S C e) (fun S1 v1 =>
          out_ter S (res_return v1))
      end

    (* Daniele: after I defined continue in JsPrettyRules this one gave
       an error. I put this 's' here, but I don't know if it's what you want. *)
    (* Martin:  That's nice, thanks :) *)

    | stat_break so =>
      out_ter S (res_break so)

    (* Daniele: same as previous one *)

    | stat_continue so =>
      out_ter S (res_continue so)

    | stat_for_in e1 e2 s =>
      arbitrary (* TODO *)

    | stat_for_in_var x e1o e2 s =>
      arbitrary (* TODO *)
  
    | stat_debugger =>
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
          out_ter S2 re2))

    | prog_function_decl f lx P =>
      arbitrary (* TODO *)

    end
  end.

End Interpreter.

