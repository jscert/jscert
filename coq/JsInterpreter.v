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

Definition extract_from_option {B : Type} `{Inhab B} (op : option B) :=
  (morph_option (fun _ : unit => arbitrary) (fun (b : B) _ => b) op) tt.

Definition if_success (o : out_interp) (K : state -> ret_or_empty -> out_interp) : out_interp :=
  match o with
  | out_ter S0 (res_normal re) => K S0 re
  | _ => o
  end.

Definition if_success_throw (o : out_interp) (K1 : state -> res -> out_interp) (K2 : state -> value -> out_interp) : out_interp :=
  match o with
  | out_ter S0 (res_normal re) => K1 S0 re
  | out_ter S0 (res_throw v) => K2 S0 v
  | _ => o
  end.

Definition if_success_return (o : out_interp) (K1 : state -> res -> out_interp) (K2 : state -> value -> out_interp) : out_interp :=
  match o with
  | out_ter S0 (res_normal re) => K1 S0 re
  | out_ter S0 (res_return v) => K2 S0 v
  | _ => o
  end.

Definition if_value (o : out_interp) (K : state -> value -> out_interp) : out_interp :=
  if_success o (fun S re =>
    match re with
    | ret_value v =>
      K S v
    | _ => out_interp_stuck
    end).

Definition if_success_bool (o : out_interp) (K1 K2 : state -> out_interp) : out_interp :=
  if_value o (fun S v =>
    match v with
    | prim_bool b =>
      (if b then K1 else K2) S
    | _ => out_interp_stuck
    end).

Definition if_success_primitive (o : out_interp) (K : state -> prim -> out_interp) : out_interp :=
  if_value o (fun S re =>
    match re with
    | value_prim w =>
      K S w
    | _ => out_interp_stuck
    end).

Definition if_defined {B : Type} (op : option B) (K : B -> out_interp) : out_interp :=
  match op with
  | None => out_interp_stuck
  | Some a => K a
  end.

Definition if_defined_else {B C : Type} (op : option B) (K : B -> C) (K' : unit -> C) : C :=
  match op with
  | None => K' tt
  | Some a => K a
  end.

Definition if_success_ret (o : out_interp) (K : state -> ret -> out_interp) : out_interp :=
  if_success o (fun S re =>
    match re with
    | ret_or_empty_ret re' => K S re'
    | _ => out_interp_stuck
    end).

Definition if_value_object (o : out_interp) (K : state -> object_loc -> out_interp) : out_interp :=
  if_value o (fun S v =>
    match v with
    | value_object l => K S l
    | _ => out_interp_stuck
    end).

Definition if_value_string (o : out_interp) (K : state -> string -> out_interp) : out_interp :=
  if_value o (fun S v =>
    match v with
    | prim_string s => K S s
    | _ => out_interp_stuck
    end).

Definition if_value_number (o : out_interp) (K : state -> number -> out_interp) : out_interp :=
  if_value o (fun S v =>
    match v with
    | prim_number n => K S n
    | _ => out_interp_stuck
    end).

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

Definition env_loc_default := 0%nat. (* It is needed to avoid using an [arbitrary] that would be extracted by an exception. *)

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

Definition run_object_call S l : option builtin :=
  object_call_ (pick (object_binds S l)).

Definition run_object_has_instance S l : option builtin :=
  object_has_instance_ (pick (object_binds S l)).

Definition run_object_scope S l : option lexical_env :=
  object_scope_ (pick (object_binds S l)).

Definition run_object_formal_parameters S l : option (list string) :=
  object_formal_parameters_ (pick (object_binds S l)).

Definition run_object_code_empty S l : bool :=
  morph_option true (fun _ => false)
    (object_code_ (pick (object_binds S l))).

Definition run_object_code S l : prog :=
  snd (extract_from_option (object_code_ (pick (object_binds S l)))).

Definition run_object_code_string S l : string :=
  fst (extract_from_option (object_code_ (pick (object_binds S l)))).

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

Definition env_record_has_binding S L x : option bool :=
  env_record_lookup None S L (fun er =>
    match er with
    | env_record_decl D =>
      Some (decide (decl_env_record_indom D x))
    | env_record_object l pt =>
      Some (object_has_prop S l x)
    end).

Fixpoint lexical_env_get_identifier_ref S X x (strict : strictness_flag) : ref :=
  match X with
  | nil =>
    ref_create_value undef x strict
  | L :: X' =>
    if env_record_has_binding S L x then
      ref_create_env_loc L x strict
    else lexical_env_get_identifier_ref S X' x strict
  end.

Definition identifier_res S C x :=
  let lex := execution_ctx_lexical_env C in
  let strict := execution_ctx_strict C in
  lexical_env_get_identifier_ref S lex x strict.

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

Definition env_record_get_binding_value S L x (strict : strictness_flag) : out_interp :=
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


Definition run_prog_type : Type := (* The functions taking such an argument can call any arbitrary code *)
  state -> execution_ctx -> prog -> out_interp.

Definition run_call_type : Type :=
  state -> execution_ctx -> builtin -> option object_loc -> option value -> list value -> out_interp.

Definition object_put (call : run_call_type) S C l x v (throw : bool) : out_interp :=
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
              call S C fc (Some fsetter) (Some (value_object l)) (v :: nil)
            | _ => out_interp_stuck
            end) else (
              let A' := prop_attributes_create_data v true true true in
              object_define_own_prop S l x A' throw
            )
        end
      )
    end) (fun S => out_reject S throw).

Definition env_record_set_mutable_binding (call : run_call_type) S C L x v (strict : strictness_flag) : out_interp :=
  match pick (env_record_binds S L) with
  | env_record_decl D =>
    let (mu, v) := read D x in
    ifb mutability_is_mutable mu then
      out_void (env_record_write_decl_env S L x mu v)
    else if strict then
      out_type_error S
    else out_ter S prim_undef
  | env_record_object l pt =>
    object_put call S C l x v strict
  end.

Definition env_record_create_mutable_binding S L x (deletable_opt : option bool) : out_interp :=
  let deletable := unsome_default false deletable_opt in
  match pick (env_record_binds S L) with
  | env_record_decl D =>
    ifb decl_env_record_indom D x then out_interp_stuck
    else
      let S' := env_record_write_decl_env S L x (mutability_of_bool deletable) undef in
      out_void S'
  | env_record_object l pt =>
    if object_has_prop S l x then out_interp_stuck
    else let An := prop_attributes_create_data undef true true deletable in
      object_define_own_prop S l x An throw_true
  end.

Definition env_record_create_set_mutable_binding (call : run_call_type) S C L x (deletable_opt : option bool) v (strict : strictness_flag) : out_interp :=
  if_success (env_record_create_mutable_binding S L x deletable_opt) (fun S re =>
    match re with
    | prim_undef =>
      env_record_set_mutable_binding call S C L x v strict
    | _ => out_interp_stuck
    end).

Definition creating_function_object_proto S l (K : state -> out_interp) : out_interp :=
  arbitrary (* TODO *).

Definition creating_function_object S (names : list string) (fb : string) p X (strict : strictness_flag) : out_interp :=
  let O := object_create builtin_function_proto "Function" true builtin_spec_op_function_get Heap.empty in
  let O1 := object_with_invokation O
    (Some builtin_spec_op_function_call)
    (Some builtin_spec_op_function_constructor)
    (Some builtin_spec_op_function_has_instance) in
  let O2 := object_with_details O1 (Some X) (Some names) (Some (fb, p)) None None None None in
  let '(l, S1) := object_alloc S O2 in
  let A1 := prop_attributes_create_data (JsNumber.of_int (List.length names)) false false false in
  if_success (object_define_own_prop S1 l "length" A1 false) (fun S2 re1 =>
    creating_function_object_proto S2 l (fun S3 =>
      if neg strict then out_ter S3 l
      else (
        let vthrower := value_object builtin_function_throw_type_error in
        let A2 := prop_attributes_create_accessor vthrower vthrower false false in
        if_success (object_define_own_prop S2 l "caller" A2 false) (fun S4 re2 =>
          if_success (object_define_own_prop S3 l "arguments" A2 false) (fun S5 re3 =>
            out_ter S5 l))))).

Definition execution_ctx_binding_instantiation (call : run_call_type) S C (funco : option object_loc) p (args : list value) : out_interp :=
  let L := hd env_loc_default (execution_ctx_variable_env C) in
  let strict := execution_ctx_strict C in
  if_success
    match funco with
    | Some func =>
      let names_option := run_object_formal_parameters S func in
      let names := unsome_default nil names_option in
      (fix setArgs S0 (args : list value) (names : list string) : out_interp :=
        match names with
        | nil => out_void S0
        | argname :: names' =>
          let v := hd undef args in
          if_success (if_defined (env_record_has_binding S L argname) (fun hb =>
            if hb then out_void S0
            else env_record_create_mutable_binding S0 L argname None)) (fun S1 re1 =>
              if_success (env_record_set_mutable_binding call S1 C L argname v strict)
              (fun S2 re2 =>
                setArgs S2 (tl args) names'))
        end) S args names
    | None => out_void S
    end (fun S1 re0 =>
      let fds := function_declarations p in
      if_success
      ((fix createExecutionContext S0 (fds : list function_declaration) : out_interp :=
        match fds with
        | nil => out_void S0
        | fd :: fds' =>
          let p' := fd_code fd in
          let strictp := function_body_is_strict p in
          let f_string := fd_string fd in
          if_value_object (creating_function_object S0 (fd_parameters fd) f_string p' (execution_ctx_variable_env C) strictp) (fun S1 fo =>
            let hb := env_record_has_binding S0 L (fd_name fd) in
            if_success (if hb then
              match run_object_get_property S builtin_global (fd_name fd) with
              | prop_descriptor_undef => out_interp_stuck
              | prop_descriptor_some A =>
                ifb prop_attributes_configurable A = Some true then (
                  let A' := prop_attributes_create_data undef true true false in (* To be reread *)
                  object_define_own_prop S1 builtin_global (fd_name fd) A' true
                ) else ifb prop_descriptor_is_accessor A \/ prop_attributes_writable A <> Some true \/ prop_attributes_enumerable A <> Some true then
                out_type_error S1
                else out_void S1
              end else env_record_create_mutable_binding S1 L (fd_name fd) (Some false)) (fun S2 re2 =>
                if_success (env_record_set_mutable_binding call S2 C L (fd_name fd) (value_object fo) strictp) (fun S3 re3 =>
                  createExecutionContext S3 fds')))
        end) S1 fds) (fun S2 re =>
        let vds := variable_declarations p in
        (fix initVariables S0 (vds : list string) : out_interp :=
          match vds with
          | nil => out_void S0
          | vd :: vds' =>
            if extract_from_option (env_record_has_binding S0 L vd) then
              initVariables S0 vds'
            else (if_success
              (env_record_create_set_mutable_binding call S0 C L vd (Some false) undef strict) (fun S1 re1 =>
                initVariables S1 vds'))
          end) S2 vds)).

Definition execution_ctx_function_call (call : run_call_type) S C (lf : object_loc) (this : value) (args : list value) (K : state -> execution_ctx -> out_interp) :=
  let p := run_object_code S lf in
  let strict := function_body_is_strict p in
  if_success (if strict then out_ter S this
    else ifb this = null \/ this = undef then out_ter S builtin_global
    else ifb type_of this = type_object then out_ter S this
    else to_object S this) (fun S1 newthis =>
      let scope := extract_from_option (run_object_scope S1 lf) in
      let (lex', S') := lexical_env_alloc_decl S1 scope in
      let C' := execution_ctx_intro_same lex' this strict in
      if_success (execution_ctx_binding_instantiation call S' C' (Some lf) p args) (fun S3 re =>
        K S3 C')).


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

Definition object_put_special v x (vnew : value) (strict : bool) : out_interp :=
  arbitrary (* TODO *).

Definition ref_put_value (call : run_call_type) S C re v : out_interp :=
  match re with
  | ret_value v => out_ref_error S
  | ret_ref r =>
    ifb ref_is_unresolvable r then (
      if ref_strict r then out_ref_error S
      else object_put call S C builtin_global (ref_name r) v throw_false)
    else
      match ref_base r with
      | ref_base_type_value (value_object l) =>
        object_put call S C l (ref_name r) v (ref_strict r)
      | ref_base_type_value (value_prim w) =>
        ifb ref_kind_of r = ref_kind_primitive_base then
          object_put_special (value_prim w) (ref_name r) v (ref_strict r)
        else out_interp_stuck
      | ref_base_type_env_loc L =>
        env_record_set_mutable_binding call S C L (ref_name r) v (ref_strict r)
      end
  end.

Definition if_success_value (o : out_interp) (K : state -> value -> out_interp) : out_interp :=
  if_success_ret o (fun S1 re1 =>
      if_success (ref_get_value S1 re1) (fun S2 re2 =>
        match re2 with
        | ret_value v => K S2 v
        | _ => out_ref_error S1
        end)).

Definition run_callable S v : option builtin :=
  match v with
  | value_prim w => None
  | value_object l =>
    run_object_call S l
  end.

Definition to_default (call : run_call_type) S C l (prefo : option preftype) : out_interp :=
  let gpref := unsome_default preftype_number prefo in
  let lpref := other_preftypes gpref in
  let gmeth := method_of_preftype gpref in
  let sub x K :=
    if_value_object (object_get S l x) (fun S1 lfo =>
      let lf := value_object lfo in
      match run_callable S lf with
      | Some fc =>
        if_success_value (call S C fc (Some lfo) (Some lf) nil) (fun S2 v =>
          match v with
          | value_prim w => out_ter S w
          | value_object l => K tt
          end)
      | None => K tt
      end) in
  sub gmeth (fun _ =>
    let lmeth := method_of_preftype lpref in
    sub lmeth (fun _ => out_type_error S)).

Definition to_primitive (call : run_call_type) S C v (prefo : option preftype) : out_interp :=
  match v with
  | value_prim w => out_ter S w
  | value_object l => to_default call S C l prefo
  end.

Definition to_number (call : run_call_type) S C v : out_interp :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_number w)
  | value_object l =>
    if_success_primitive (to_primitive call S C (value_object l) (Some preftype_number)) (fun S1 w =>
      out_ter S (convert_prim_to_number w))
  end.

Definition to_integer (call : run_call_type) S C v : out_interp :=
  if_success (to_number call S C v) (fun S1 re1 =>
    match re1 with
    | prim_number n =>
      out_ter S (convert_number_to_integer n)
    | _ => out_interp_stuck
    end).

Definition to_string (call : run_call_type) S C v : out_interp :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_string w)
  | value_object l =>
    if_success_primitive (to_primitive call S C (value_object l) (Some preftype_string)) (fun S1 w =>
      out_ter S (convert_prim_to_string w))
  end.


End LexicalEnvironments.


Section IntermediaryFunctions.

Definition run_binary_op (call : run_call_type) S C (op : binary_op) v1 v2 : out_interp :=
  match op with

  | binary_op_add =>
    if_value (to_primitive call S C v1 None) (fun S1 re1 =>
      if_value (to_primitive call S1 C v2 None) (fun S2 re2 =>
        ifb type_of v1 = type_string \/ type_of v2 = type_string then
          if_value_string (to_string call S2 C v1) (fun S3 s1 =>
            if_value_string (to_string call S3 C v2) (fun S4 s2 =>
              out_ter S4 (s1 ++ s2)))
        else
          if_value_number (to_number call S2 C v1) (fun S3 n1 =>
            if_value_number (to_number call S3 C v2) (fun S4 n2 =>
              out_ter S4 (JsNumber.add n1 n2)))))

  | binary_op_mult =>
    if_value_number (to_number call S C v1) (fun S1 n1 =>
      if_value_number (to_number call S1 C v2) (fun S2 n2 =>
        out_ter S2 (JsNumber.mult n1 n2)))

  | binary_op_div =>
    if_value_number (to_number call S C v1) (fun S1 n1 =>
      if_value_number (to_number call S1 C v2) (fun S2 n2 =>
        out_ter S2 (JsNumber.div n1 n2)))

  | binary_op_mod =>
    if_value_number (to_number call S C v1) (fun S1 n1 =>
      if_value_number (to_number call S1 C v2) (fun S2 n2 =>
        out_ter S2 (JsNumber.fmod n1 n2)))

  | binary_op_sub =>
    if_value_number (to_number call S C v1) (fun S1 n1 =>
      if_value_number (to_number call S1 C v2) (fun S2 n2 =>
        out_ter S2 (JsNumber.sub n1 n2)))

  | binary_op_and | binary_op_or => arbitrary (* Lazy operators are already dealt with at this point. *)

  | _ => arbitrary (* TODO *)

  end.

Definition is_lazy_op (op : binary_op) : option bool :=
  match op with
  | binary_op_and => Some false
  | binary_op_or => Some true
  | _ => None
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
    let run_call' := run_call max_step' in
    match e with

    | expr_literal i =>
      out_ter S (convert_literal_to_prim i)

    | expr_variable x =>
      out_ter S (identifier_res S C x)

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

    | expr_binary_op e1 op e2 =>
      match is_lazy_op op with
      | None =>
        if_success_value (run_expr' S C e1) (fun S1 v1 =>
          if_success_value (run_expr' S1 C e2) (fun S2 v2 =>
            run_binary_op run_call' S2 C op v1 v2))
      | Some b_ret =>
        if_success_value (run_expr' S C e1) (fun S1 v1 =>
          let b1 := convert_value_to_boolean v1 in
          ifb b1 = b_ret then out_ter S1 v1
          else
            if_success_value (run_expr' S1 C e2) (fun S2 v2 =>
              out_ter S2 v2))
      end

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
        match re1 with
        | ret_or_empty_empty => out_interp_stuck
        | ret_or_empty_ret re =>
          let follow S re' :=
            match re' with
            | ret_or_empty_ret (ret_value v) =>
              if_success (ref_put_value run_call' S C re v) (fun S' re2 =>
               out_ter S' v)
            | _ => out_interp_stuck
            end in
          match opo with
          | None =>
            if_success_value (run_expr' S1 C e2) follow
          | Some op =>
            if_success_value (out_ter S1 re) (fun S2 v1 =>
              if_success_value (run_expr' S2 C e2) (fun S3 v2 =>
                if_success (run_binary_op run_call' S3 C op v1 v2) follow))
          end
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
    let run_expr' := run_expr max_step' in
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    match t with

    | stat_expr e =>
      run_expr' S C e

    | stat_skip =>
      out_ter S ret_empty

    | stat_var_decl xeos =>
      (fix run_var_decl S0 xeos : out_interp :=
        match xeos with
        | nil => out_ter S0 ret_empty
        | (x, eo) :: xeos' =>
          if_success (match eo with
            | None => out_ter S0 undef
            | Some e =>
              if_success_value (run_expr' S0 C e) (fun S1 v =>
                let ir := identifier_res S1 C x in
                if_success (ref_put_value run_call' S1 C ir v) (fun S2 re =>
                  out_ter S1 undef))
            end) (fun S1 re =>
              run_var_decl S1 xeos')
        end) S xeos

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
          | _ => out_interp_stuck
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
            (env_record_create_set_mutable_binding run_call' S C L x None v throw_irrelevant)
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

    | stat_break so =>
      out_ter S (res_break so)

    | stat_continue so =>
      out_ter S (res_continue so)

    | stat_for_in e1 e2 s =>
      arbitrary (* TODO *)

    | stat_for_in_var x e1o e2 s =>
      arbitrary (* TODO *)
  
    | stat_debugger =>
      out_ter S ret_empty

    end
  end

with run_prog (max_step : nat) S C p : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
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
  end

with run_call (max_step : nat) S C (builtinid : builtin) (lfo : option object_loc) (vo : option value) (args : list value) : out_interp :=
  match max_step with
  | O => out_interp_bottom
  | S max_step' =>
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    match builtinid with

    | builtin_spec_op_object_get =>
      let lf := extract_from_option lfo in
      let this := extract_from_option vo in
      execution_ctx_function_call run_call' S C lf this args (fun S1 C1 =>
        if run_object_code_empty S1 lf then
          out_ter S1 (res_normal undef)
        else (
          let p := run_object_code S1 lf in
          if_success_return (run_prog' S1 C1 p) (fun S2 re =>
            out_ter S (res_normal undef)) (fun S2 v =>
            out_ter S (res_normal v))))

    | _ =>
      arbitrary (* TODO *)

    end
  end.

End Interpreter.

