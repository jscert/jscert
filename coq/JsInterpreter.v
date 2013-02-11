Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSyntax JsSyntaxAux JsPreliminary JsPreliminaryAux.

(**************************************************************)
(** ** Implicit Types -- copied from JsPreliminary *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type B : builtin.
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
(** ** Some functions to be implemented (or extracted differently). *)

Parameter JsNumber_to_int : JsNumber.number -> (* option? *) int.
(* It should never return an option, but its result will is a pain to be used... -- Martin *)


(**************************************************************)
(** ** Some types used by the interpreter *)

Inductive result :=
  | result_normal : out -> result
  | result_stuck
  | result_bottom.

(* Coercion *)

Coercion result_normal : out >-> result.

(* Inhabited *)

Global Instance result_inhab : Inhab result.
Proof. applys prove_Inhab result_stuck. Qed.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section InterpreterEliminations.

(**************************************************************)
(** Generic constructions *)

Definition get_arg := get_nth undef.

(**************************************************************)
(** Monadic constructors *)

Definition if_success_state rv (o : result) (K : state -> resvalue -> result) : result :=
  match o with
  | out_ter S0 R =>
    match res_type R with
    | restype_normal =>
      let rv' := res_value R in
      K S0 (ifb rv' = resvalue_empty then rv else rv')
    | _ => o
    end
  | _ => o
  end.

Definition if_success := if_success_state resvalue_empty.

Definition if_success_or_throw (o : result) (K1 : state -> resvalue -> result) (K2 : state -> value -> result) : result :=
  match o with
  | out_ter S0 R =>
    match res_type R with
    | restype_normal => K1 S0 (res_value R)
    | restype_throw =>
      match res_value R with
      | resvalue_value v => K2 S0 v
      | _ => result_stuck
      end
    | _ => o
    end
  | _ => o
  end.

Definition if_success_or_return (o : result) (K1 : state -> resvalue -> result) (K2 : state -> value -> result) : result :=
  match o with
  | out_ter S0 R =>
    match res_type R with
    | restype_normal => K1 S0 (res_value R)
    | restype_return =>
      match res_value R with
      | resvalue_value v => K2 S0 v
      | _ => result_stuck
      end
    | _ => o
    end
  | _ => o
  end.

Definition if_success_or_break (o : result) (K1 : state -> resvalue -> result) (K2 : state -> res -> result) : result :=
  match o with
  | out_ter S0 R =>
    match res_type R with
    | restype_normal => K1 S0 (res_value R)
    | restype_break => K2 S0 R
    | _ => o
    end
  | _ => o
  end.

Definition if_success_while rv (o : result) (K : state -> resvalue -> result) : result :=
  match o with
  | out_ter S0 R =>
    let rv' := res_value R in
    let rvf := ifb rv' = resvalue_empty then rv else rv' in
    match res_type R with
    | restype_normal =>
      K S0 rvf
    | restype_break =>
      out_ter S0 (res_with_value R rvf)
    | _ => o
    end
  | _ => o
  end.

Definition if_value (o : result) (K : state -> value -> result) : result :=
  if_success o (fun S rv =>
    match rv with
    | resvalue_value v =>
      K S v
    | _ => result_stuck
    end).

Definition if_success_bool (o : result) (K1 K2 : state -> result) : result :=
  if_value o (fun S v =>
    match v with
    | prim_bool b =>
      (if b then K1 else K2) S
    | _ => result_stuck
    end).

Definition if_success_primitive (o : result) (K : state -> prim -> result) : result :=
  if_value o (fun S v =>
    match v with
    | value_prim w =>
      K S w
    | _ => result_stuck
    end).

Definition if_defined {B : Type} (op : option B) (K : B -> result) : result :=
  match op with
  | None => result_stuck
  | Some a => K a
  end.

Definition if_defined_else {B C : Type} (op : option B) (K : B -> C) (K' : unit -> C) : C :=
  match op with
  | None => K' tt
  | Some a => K a
  end.

Definition if_object (o : result) (K : state -> object_loc -> result) : result :=
  if_value o (fun S v =>
    match v with
    | value_object l => K S l
    | _ => result_stuck
    end).

Definition if_string (o : result) (K : state -> string -> result) : result :=
  if_value o (fun S v =>
    match v with
    | prim_string s => K S s
    | _ => result_stuck
    end).

Definition if_number (o : result) (K : state -> number -> result) : result :=
  if_value o (fun S v =>
    match v with
    | prim_number n => K S n
    | _ => result_stuck
    end).

Definition if_primitive (o : result) (K : state -> prim -> result) : result :=
  if_value o (fun S v =>
    match v with
    | value_prim w => K S w
    | _ => result_stuck
    end).

Definition env_loc_default := 0%nat. (* It is needed to avoid using an [arbitrary] that would be extracted by an exception. *)

End InterpreterEliminations.

(**************************************************************)
(** Operations on objects *)

Section LexicalEnvironments.

Definition run_object_method (Proj : object -> builtin) S l : builtin :=
  Proj (pick (object_binds S l)).

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

Definition run_object_code S l : funcbody :=
  extract_from_option (object_code_ (pick (object_binds S l))).

Definition run_object_properties S l : object_properties_type :=
  object_properties_ (pick (object_binds S l)).

Definition run_object_heap_set_properties S l P' : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_with_properties O P').


(**************************************************************)
(** Operations on environments *)

Definition run_decl_env_record_binds_value Ed x : value :=
  snd (pick (binds Ed x)).

Definition run_object_get_own_prop_base P x : full_descriptor :=
  match read_option P x with
  | None => full_descriptor_undef
  | Some A => full_descriptor_some A
  end.

Definition run_object_get_own_property_default S l x : full_descriptor :=
  run_object_get_own_prop_base (run_object_properties S l) x.

Definition run_object_get_own_property S l x : full_descriptor :=
  let sclass := run_object_class S l in
  let D := run_object_get_own_property_default S l x in
  ifb sclass = "String" then (
    ifb D <> full_descriptor_undef then D
    else let ix := convert_primitive_to_integer x in
    ifb prim_string x <> convert_prim_to_string (JsNumber.absolute ix) then
      full_descriptor_undef
    else (
      match run_object_prim_value S l with
      | prim_string s =>
        let len : int := String.length s in
        let i := JsNumber_to_int ix in
        ifb len <= i then full_descriptor_undef
        else let s' := string_sub s i 1 in
          attributes_data_intro s' false true false
      | _ => arbitrary
      end
    )
  ) else D.

Definition object_get_property_body run_object_get_property S v x : full_descriptor :=
  match v with
  | value_prim w =>
    ifb v = null then full_descriptor_undef
    else arbitrary
  | value_object l =>
    let D := run_object_get_own_property S l x in
    ifb D = full_descriptor_undef then (
      let lproto := run_object_proto S l in
      run_object_get_property S lproto x
    ) else D
  end.

Definition run_object_get_property := FixFun3 object_get_property_body.

Definition object_has_prop S l x : bool :=
  let D := run_object_get_property S (value_object l) x in
  decide (D <> full_descriptor_undef).

Definition object_proto_is_prototype_of_body run_object_proto_is_prototype_of S l0 l : result :=
  match run_object_proto S  l  with
  | null => out_ter S false
  | value_object l' =>
    ifb l' = l0 then out_ter S true
    else run_object_proto_is_prototype_of S l0 l'
  | _ => result_stuck
  end.

Definition run_object_proto_is_prototype_of := FixFun3 object_proto_is_prototype_of_body.

Definition env_record_lookup {B : Type} (d : B) S L (K : env_record -> B) : B :=
  match read_option (state_env_record_heap S) L with
  | Some E => K E
  | None => d
  end.

Definition env_record_has_binding S L x : bool :=
  env_record_lookup (fun _ : unit => arbitrary) S L (fun E _ =>
    match E with
    | env_record_decl Ed =>
      decide (decl_env_record_indom Ed x)
    | env_record_object l pt =>
      object_has_prop S l x
    end) tt.

Fixpoint lexical_env_get_identifier_ref S X x str : ref :=
  match X with
  | nil =>
    ref_create_value undef x str
  | L :: X' =>
    if env_record_has_binding S L x then
      ref_create_env_loc L x str
    else lexical_env_get_identifier_ref S X' x str
  end.

Definition env_record_delete_binding S L x : result :=
  env_record_lookup (fun _ : unit => arbitrary) S L (fun E _ =>
    match E return result with
    | env_record_decl Ed =>
      match read_option Ed x with
      | None =>
        out_ter S true
      | Some (mutability_nondeletable, v) =>
        out_ter S false
      | Some (mu, v) =>
        out_ter (state_with_env_record_heap S
          (write (state_env_record_heap S) L
            (env_record_decl (rem Ed x)))) true
      end
    | env_record_object l pt =>
      result_stuck
    end) tt.

Definition identifier_res S C x :=
  let X := execution_ctx_lexical_env C in
  let str := execution_ctx_strict C in
  lexical_env_get_identifier_ref S X x str.

Definition object_get S v x : result :=
  match run_object_get_property S v x with
  | full_descriptor_undef => out_ter S undef
  | full_descriptor_some (attributes_data_of Ad) =>
    out_ter S (attributes_data_value Ad)
  | full_descriptor_some (attributes_accessor_of Aa) =>
    arbitrary (* TODO *)
  end.

(* TODO:  Understand this function.
Definition object_get (run_call' : run_call_type) S C v x : result :=
  match v with
  | value_object l =>
    let vthis := v in
    match run_object_method object_get_ S l with
    | builtin_default_get =>
      match run_object_get_property S l x with
      | full_descriptor_undef => out_ter S undef
      | attributes_data_of Ad =>
        out_ter S (attributes_data_value Ad)
      | attributes_accessor_of Aa =>
        match attributes_accessor_get Aa with
        | undef => out_ter S undef
        | value_object lf =>
          run_call' S C
        end
      end
    | _ =>
      arbitrary (* TODO *)
    end
  | value_prim _ => result_stuck
  end.
*)


(**************************************************************)
(** Conversions *)

Definition prim_new_object S w : result :=
  arbitrary (* TODO *).

Definition to_object S v : result :=
  match v with
  | prim_null | prim_undef => out_type_error S
  | value_prim w =>
    prim_new_object S w
  | value_object l => out_ter S l
  end.

Definition prim_value_get S v x : result :=
  if_object (to_object S v) (fun S' l =>
    object_get S' l x).

Definition run_value_viewable_as_prim s S v : option prim :=
  match v with
  | value_prim w => Some w
  | value_object l =>
    let s := run_object_class S l in
    match run_object_prim_value S l with
    | value_prim w => Some w
    | _ => None
    end
  end.


(**************************************************************)
(** Built-in constructors *)

Definition call_object_new S v : result :=
  match type_of v return result with
  | type_object => out_ter S v
  | type_string | type_bool | type_number =>
    to_object S v
  | type_null | type_undef =>
    let O := object_new builtin_object_proto "Object" in
    let (l, S') := object_alloc S O in
    out_ter S' l
  end.

Definition bool_proto_value_of_call S C : result :=
  let v := execution_ctx_this_binding C in
  match run_value_viewable_as_prim "Boolean" S v with
  | Some (prim_bool b) => out_ter S b
  | _ => out_type_error S
  end.

Definition constructor_builtin S C B (args : list value) : result :=
  match B with

  | builtin_object_call =>
    let v := get_arg 0 args in
    match v with
    | null | undef =>
      call_object_new S v
    | _ => to_object S v
    end

  | builtin_object_new =>
    let v := get_arg 0 args in
    call_object_new S v

  | _ => arbitrary (* TODO:  Which ones of them return [result_stuck]? *)

  end.


(**************************************************************)

Definition env_record_get_binding_value S L x str : result :=
  env_record_lookup result_stuck S L (fun er =>
    match er with
    | env_record_decl Ed =>
      let (mu, v) := read Ed x in
      ifb mu = mutability_uninitialized_immutable then
        out_error_or_cst S str builtin_ref_error undef
      else out_ter S v
    | env_record_object l pt =>
      if object_has_prop S l x then
        object_get S l x
      else out_error_or_cst S str builtin_ref_error undef
    end).

Definition object_can_put S l x : result :=
  let D := run_object_get_own_property S l x in
  let oe := run_object_extensible S l in
  match D with
  | full_descriptor_some A =>
    match A with
    | attributes_accessor_of Aa =>
      out_ter S (decide (attributes_accessor_set Aa = undef))
    | attributes_data_of Ad =>
      out_ter S (prim_bool (attributes_data_writable Ad))
    end
  | full_descriptor_undef =>
    let lproto := run_object_proto S l in
    ifb lproto = null then out_ter S oe
    else (
      let Anproto := run_object_get_property S lproto x in
      match Anproto with
      | full_descriptor_undef => out_ter S oe
      | full_descriptor_some A =>
        match A with
        | attributes_accessor_of Aa =>
          out_ter S (decide (attributes_accessor_set Aa = undef))
        | attributes_data_of Ad =>
          out_ter S (if oe then false else prim_bool (attributes_data_writable Ad))
        end
      end
    )
  end.

Definition object_define_own_prop S l x Desc str : result :=
  let D := run_object_get_own_property S l x in
  let extensible := run_object_extensible S l in
  (* Note that Array will have a special case there. *)
  match D with
  | full_descriptor_undef =>
    if extensible then (
      let A :=
        ifb descriptor_is_generic Desc \/ descriptor_is_data Desc
        then attributes_data_of_descriptor Desc : attributes
        else attributes_accessor_of_descriptor Desc in
      let S' := pick (object_set_property S l x A) in
      out_ter S' true
    ) else out_reject S str
  | full_descriptor_some A =>
    let dop_write S' A' :=
      let A'' := attributes_update A Desc in
      let S'' := pick (object_set_property S' l x A'') in
      out_ter S'' true in
    ifb descriptor_contains A Desc then
      out_ter S true
    else ifb attributes_change_enumerable_on_non_configurable A Desc then
      out_reject S str
    else ifb descriptor_is_generic Desc then
      dop_write S A
    else ifb attributes_is_data A <> descriptor_is_data Desc then (
     if neg (attributes_configurable A) then
       out_reject S str
     else (
      let A':=
        match A return attributes with
        | attributes_data_of Ad => attributes_accessor_of_attributes_data Ad
        | attributes_accessor_of Aa => attributes_data_of_attributes_accessor Aa
        end in
      let S' := pick (object_set_property S l x A') in
      dop_write S' A'
    )) else
      match A with
      | attributes_data_of Ad =>
        ifb descriptor_is_data Desc then (
          ifb attributes_change_data_on_non_configurable Ad Desc then
            out_reject S str
          else
            dop_write S Ad
        ) else result_stuck
      | attributes_accessor_of Aa =>
        ifb descriptor_is_accessor Desc then (
          ifb attributes_change_accessor_on_non_configurable Aa Desc then
            out_reject S str
          else
            dop_write S Aa
        ) else result_stuck
      end
  end.


(**************************************************************)

(* The functions taking such arguments can call any arbitrary code,
   i.e. can also call arbitrary pogram and expression.  They thus need
   a pointer to the main functions.  Those types are just the ones of
   those main functions. *)

Definition run_expr_type : Type :=
  state -> execution_ctx -> expr -> result.

Definition run_prog_type : Type :=
  state -> execution_ctx -> prog -> result.

Definition run_call_type : Type :=
  state -> execution_ctx -> builtin -> option object_loc -> option value -> list value -> result.


(**************************************************************)

Definition ref_get_value S rv : result :=
  match rv with
  | resvalue_empty => result_stuck
  | resvalue_value v => out_ter S v
  | resvalue_ref r =>
    match ref_kind_of r with
    | ref_kind_null | ref_kind_undef => out_ref_error S
    | ref_kind_primitive_base | ref_kind_object =>
      match ref_base r with
      | ref_base_type_value v =>
        (ifb ref_has_primitive_base r then prim_value_get
        else object_get) S v (ref_name r)
      | ref_base_type_env_loc L =>
        env_record_get_binding_value S L (ref_name r) (ref_strict r)
      end
    | ref_kind_env_record =>
      match ref_base r with
      | ref_base_type_value v => result_stuck
      | ref_base_type_env_loc L =>
        env_record_get_binding_value S L (ref_name r) (ref_strict r)
      end
    end
  end.

Definition object_put (run_call' : run_call_type) S C (Bo : option builtin) l x v str : result :=
  match morph_option (run_object_method object_put_ S l) id Bo with

  | builtin_default_put =>
    if_success_bool (object_can_put S l x) (fun S' =>
      match run_object_get_own_property S' l x with (* TODO:  Fix this after the rules will be. *)
      | attributes_data_of Ad =>
        let Desc := descriptor_intro (Some v) None None None None None in
        if_success (object_define_own_prop S' l x Desc str) (fun S2 rv =>
          out_void S2)
      | attributes_accessor_of Aa =>
        match run_object_get_property S' (value_object l) x with
        | attributes_accessor_of Aa =>
          match attributes_accessor_set Aa with
          | value_object lfsetter =>
            arbitrary (* Waiting for the spec.  TODO:  run_call' S' C lfsetter *)
          | _ => result_stuck
          end
        | attributes_data_of Ad =>
          arbitrary (* TODO *)
        | full_descriptor_none => result_stuck
        end
      | full_descriptor_undef =>
        let Ad := attributes_data_intro v true true true in
        object_define_own_prop S' l x Ad str
      end)
      (fun S' => out_error_or_void S str builtin_type_error)

    | _ => arbitrary (* TODO *)

    end.

Definition env_record_set_mutable_binding (run_call' : run_call_type) S C L x v str : result :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    let (mu, v_old) := read Ed x in
    ifb mutability_is_mutable mu then
      out_void (env_record_write_decl_env S L x mu v)
    else if str then
      out_type_error S
    else out_ter S prim_undef
  | env_record_object l pt =>
    object_put run_call' S C None l x v str
  end.

Definition prim_value_put (run_call' : run_call_type) S C w x v str : result :=
  if_object (to_object S w) (fun S1 l =>
    object_put run_call' S1 C (Some builtin_default_put) l x v str).

Definition ref_put_value (run_call' : run_call_type) S C rv v : result :=
  match rv with
  | resvalue_value v => out_ref_error S
  | resvalue_ref r =>
    ifb ref_is_unresolvable r then (
      if ref_strict r then out_ref_error S
      else object_put run_call' S C None builtin_global (ref_name r) v throw_false)
    else
      match ref_base r with
      | ref_base_type_value (value_object l) =>
        object_put run_call' S C None l (ref_name r) v (ref_strict r)
      | ref_base_type_value (value_prim w) =>
        ifb ref_kind_of r = ref_kind_primitive_base then
          prim_value_put run_call' S C w (ref_name r) v (ref_strict r)
        else result_stuck
      | ref_base_type_env_loc L =>
        env_record_set_mutable_binding run_call' S C L (ref_name r) v (ref_strict r)
      end
  | resvalue_empty => result_stuck
  end.

Definition if_success_value (o : result) (K : state -> value -> result) : result :=
  if_success o (fun S1 rv1 =>
    if_success (ref_get_value S1 rv1) (fun S2 rv2 =>
      match rv2 with
      | resvalue_value v => K S2 v
      | _ => out_ref_error S2
      end)).


Definition env_record_create_mutable_binding S L x (deletable_opt : option bool) : result :=
  let deletable := unsome_default false deletable_opt in
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    ifb decl_env_record_indom Ed x then result_stuck
    else
      let S' := env_record_write_decl_env S L x (mutability_of_bool deletable) undef in
      out_void S'
  | env_record_object l pt =>
    if object_has_prop S l x then result_stuck
    else let A := attributes_data_intro undef true true deletable in
      object_define_own_prop S l x A throw_true
  end.

Definition env_record_create_set_mutable_binding (run_call' : run_call_type) S C L x (deletable_opt : option bool) v str : result :=
  if_success (env_record_create_mutable_binding S L x deletable_opt) (fun S rv =>
    match rv with
    | prim_undef =>
      env_record_set_mutable_binding run_call' S C L x v str
    | _ => result_stuck
    end).

Definition env_record_create_immutable_binding S L x : result :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    ifb decl_env_record_indom Ed x then result_stuck
    else out_void (
      env_record_write_decl_env S L x mutability_uninitialized_immutable undef)
  | _ => result_stuck
  end.

Definition env_record_initialize_immutable_binding S L x v : result :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    (* In contrary to the rules, no check is performed there, is that a problem? -- Martin *)
    let S' := env_record_write_decl_env S L x mutability_immutable v in
    out_void S'
  | _ => result_stuck
  end.

Definition env_record_void  S L x v : result :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    let v_old := run_decl_env_record_binds_value Ed x in
    out_void (env_record_write_decl_env S L x mutability_immutable v)
  | _ => result_stuck
  end.

Definition creating_function_object_proto S C l (K : state -> result) : result :=
  if_object (constructor_builtin S C builtin_object_new nil) (fun S1 lproto =>
    let A1 := attributes_data_intro (value_object l) true false true in
    if_success (object_define_own_prop S1 lproto "constructor" A1 false) (fun S2 rv1 =>
      let A2 := attributes_data_intro (value_object lproto) true false false in
      if_success (object_define_own_prop S2 l "prototype" A2 false) (fun S3 rv2 =>
        K S3))).

Definition creating_function_object S C (names : list string) (bd : funcbody) X str : result :=
  let O := object_create builtin_function_proto "Function" true Heap.empty in
  let O1 := object_with_invokation O
    (Some builtin_spec_op_function_constructor)
    (Some builtin_spec_op_function_call)
    (Some builtin_spec_op_function_has_instance) in
  let O2 := object_with_details O1 (Some X) (Some names) (Some bd) None None None None in
  let (l, S1) := object_alloc S O2 in
  let A1 := attributes_data_intro (JsNumber.of_int (List.length names)) false false false in
  if_success (object_define_own_prop S1 l "length" A1 false) (fun S2 rv1 =>
    creating_function_object_proto S2 C l (fun S3 =>
      if negb str then out_ter S3 l
      else (
        let vthrower := value_object builtin_function_throw_type_error in
        let A2 := attributes_accessor_intro vthrower vthrower false false in
        if_success (object_define_own_prop S3 l "caller" A2 false) (fun S4 rv2 =>
          if_success (object_define_own_prop S4 l "arguments" A2 false) (fun S5 rv3 =>
            out_ter S5 l))))).

Fixpoint execution_ctx_binding_instantiation_set_args (run_call' : run_call_type) S C L (args : list value) (names : list string) str : result :=
  match names with
  | nil => out_void S
  | argname :: names' =>
    let v := hd undef args in
    let hb := env_record_has_binding S L argname in
    if_success
      (if hb then out_void S
      else env_record_create_mutable_binding S L argname None) (fun S1 rv1 =>
        if_success (env_record_set_mutable_binding run_call' S1 C L argname v str)
        (fun S2 rv2 =>
          execution_ctx_binding_instantiation_set_args run_call' S2 C L (tl args) names' str))
  end.

Fixpoint execution_ctx_binding_instantiation_create_execution_ctx (run_call' : run_call_type) S C L (fds : list funcdecl) : result :=
  arbitrary (* TODO
  match fds with
  | nil => out_void S
  | fd :: fds' =>
    let fb := funcdecl_body fd in
    let fn := funcdecl_name fd in
    let strb := funcbody_is_strict fb in
    if_object (creating_function_object S (funcdecl_parameters fd) fb (execution_ctx_variable_env C) strb) (fun S1 fo =>
      let hb := env_record_has_binding S L fn in
      if_success (if hb then
        match run_object_get_property S builtin_global fn with
        | full_descriptor_undef => result_stuck
        | full_descriptor_some A =>
          if attributes_configurable A then (
            let A' := attributes_data_intro undef true true false in (* To be reread *)
            object_define_own_prop S1 builtin_global fn A' true
          ) else ifb descriptor_is_accessor A \/ attributes_writable A <> Some true \/ attributes_enumerable A <> Some true then (* TODO:  This rule has unfortunately no meaning.  Read it directly from the specifiaction 5e iv of execution_ctx_binding_instantiation. *)
          out_type_error S1
          else out_void S1
        end else env_record_create_mutable_binding S1 L fn (Some false)) (fun S2 rv2 =>
          if_success (env_record_set_mutable_binding run_call' S2 C L fn (value_object fo) strb) (fun S3 rv3 =>
            execution_ctx_binding_instantiation_create_execution_ctx run_call' S3 C L fds')))
  end *).

Fixpoint execution_ctx_binding_instantiation_init_vars (run_call' : run_call_type) S C L (vds : list string) str : result :=
  match vds with
  | nil => out_void S
  | vd :: vds' =>
    if env_record_has_binding S L vd then
      execution_ctx_binding_instantiation_init_vars run_call' S C L vds' str
    else
      if_success (env_record_create_set_mutable_binding run_call' S C L vd (Some false) undef str) (fun S1 rv1 =>
        execution_ctx_binding_instantiation_init_vars run_call' S1 C L vds' str)
  end.

Definition execution_ctx_binding_instantiation (run_call' : run_call_type) S C (funco : option object_loc) p (args : list value) : result :=
  let L := hd env_loc_default (execution_ctx_variable_env C) in
  let str := execution_ctx_strict C in
  if_success
    match funco with
    | Some func =>
      let names_option := run_object_formal_parameters S func in
      let names := unsome_default nil names_option in
      execution_ctx_binding_instantiation_set_args run_call' S C L args names str
    | None => out_void S
    end (fun S1 re0 =>
      let fds := prog_funcdecl p in
      if_success (execution_ctx_binding_instantiation_create_execution_ctx run_call' S1 C L fds) (fun S2 rv =>
        let vds := prog_vardecl p in
        execution_ctx_binding_instantiation_init_vars run_call' S2 C L vds str)).

Definition execution_ctx_function_call (run_call' : run_call_type) S C (lf : object_loc) (this : value) (args : list value) (K : state -> execution_ctx -> result) :=
  let bd := run_object_code S lf in
  let str := funcbody_is_strict bd in
  let newthis :=
    if str then this
    else ifb this = null \/ this = undef then builtin_global
    else ifb type_of this = type_object then this
    else arbitrary in
  let scope := extract_from_option (run_object_scope S lf) in
  let (lex', S1) := lexical_env_alloc_decl S scope in
  let C1 := execution_ctx_intro_same lex' this str in
  if_success (execution_ctx_binding_instantiation run_call' S1 C1 (Some lf) (funcbody_prog bd) args) (fun S2 rv =>
    K S2 C1).

Fixpoint run_spec_object_has_instance_loop (max_step : nat) S lv lo : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>

    match run_object_proto S lv with
    | null => out_ter S false
    | value_object proto =>
      ifb proto = lo then out_ter S true
      else run_spec_object_has_instance_loop max_step' S proto lo
    | _ => result_stuck
    end

  end.

Definition run_spec_object_has_instance (max_step : nat) B S l v : result :=
  match B with

  | builtin_spec_op_function_has_instance =>
    match v with
    | value_prim w => out_ter S false
    | value_object lv =>
      if_object (object_get S l "prototype") (fun S1 lo =>
        run_spec_object_has_instance_loop max_step S1 lv lo)
    end

  | _ => arbitrary (* TODO *)

  end.


(**************************************************************)
(** Conversions *)

Definition to_default (run_call' : run_call_type) S C l (prefo : option preftype) : result :=
  let gpref := unsome_default preftype_number prefo in
  let lpref := other_preftypes gpref in
  let gmeth := method_of_preftype gpref in
  let sub x K :=
    if_object (object_get S l x) (fun S1 lfo =>
      let lf := value_object lfo in
      match run_callable S lf with
      | Some fc =>
        if_success_value (run_call' S C fc (Some lfo) (Some lf) nil) (fun S2 v =>
          match v with
          | value_prim w => out_ter S w
          | value_object l => K tt
          end)
      | None => K tt
      end) in
  sub gmeth (fun _ =>
    let lmeth := method_of_preftype lpref in
    sub lmeth (fun _ => out_type_error S)).

Definition to_primitive (run_call' : run_call_type) S C v (prefo : option preftype) : result :=
  match v with
  | value_prim w => out_ter S w
  | value_object l => to_default run_call' S C l prefo
  end.

Definition to_number (run_call' : run_call_type) S C v : result :=
  match v with
  | value_prim w =>
      out_ter S (convert_prim_to_number w)
  | value_object l =>
     if_success_primitive (to_primitive run_call' S C (value_object l) (Some preftype_number)) (fun S1 w =>
        out_ter S (convert_prim_to_number w))
  end.

Definition to_integer (run_call' : run_call_type) S C v : result :=
  if_success (to_number run_call' S C v) (fun S1 rv1 =>
    match rv1 with
    | prim_number n =>
      out_ter S (convert_number_to_integer n)
    | _ => result_stuck
    end).

Definition to_int32 (run_call' : run_call_type) S C v (K : state -> int -> result) : result :=
  if_number (to_number run_call' S C v) (fun S' n =>
    K S' (JsNumber.to_int32 n)).

Definition to_uint32 (run_call' : run_call_type) S C v (K : state -> int -> result) : result :=
  if_number (to_number run_call' S C v) (fun S' n =>
    K S' (JsNumber.to_uint32 n)).

Definition to_string (run_call' : run_call_type) S C v : result :=
  match v with
  | value_prim w =>
      out_ter S (convert_prim_to_string w)
  | value_object l =>
      if_success_primitive (to_primitive run_call' S C (value_object l) (Some preftype_string)) (fun S1 w =>
        out_ter S (convert_prim_to_string w))
  end.

Definition env_record_implicit_this_value S L : value :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed => undef
  | env_record_object l provide_this =>
      if provide_this
        then value_object l
        else undef
  end.

Fixpoint run_list_expr (run_expr : state -> execution_ctx -> expr -> result)
  S1 C (vs : list value) (es : list expr)
  (K : state -> list value -> result) : result :=
  match es with
  | nil => K S1 (LibList.rev vs)
  | e :: es' =>
    if_success_value (run_expr S1 C e) (fun S2 v =>
      run_list_expr run_expr S2 C (v :: vs) es' K)
  end.

End LexicalEnvironments.


Section Operators.

(**************************************************************)
(** Operators *)

Definition is_lazy_op (op : binary_op) : option bool :=
  match op with
  | binary_op_and => Some false
  | binary_op_or => Some true
  | _ => None
  end.

Definition get_puremath_op (op : binary_op) : number -> number -> number :=
  match op with
  | binary_op_mult => JsNumber.mult
  | binary_op_div => JsNumber.div
  | binary_op_mod => JsNumber.fmod
  | binary_op_sub => JsNumber.sub
  | _ => arbitrary
  end.

Definition get_inequality_op (op : binary_op) : bool * bool :=
  match op with
  | binary_op_lt => (false, false)
  | binary_op_gt => (true, false)
  | binary_op_le => (true, true)
  | binary_op_ge => (false, true)
  | _ => arbitrary
  end.

Definition get_shift_op (op : binary_op) : bool * (int -> int -> int) :=
  match op with
  | binary_op_left_shift => (false, JsNumber.int32_left_shift)
  | binary_op_right_shift => (false, JsNumber.int32_right_shift)
  | binary_op_unsigned_right_shift => (true, JsNumber.uint32_right_shift)
  | _ => arbitrary
  end.

Definition get_bitwise_op (op : binary_op) : int -> int -> int :=
  match op with
  | binary_op_bitwise_and => JsNumber.int32_bitwise_and
  | binary_op_bitwise_or => JsNumber.int32_bitwise_or
  | binary_op_bitwise_xor => JsNumber.int32_bitwise_xor
  | _ => arbitrary
  end.


Definition convert_twice {A : Type} (ifv : result -> (state -> A -> result) -> result) (KC : state -> value -> result) S v1 v2 (K : state -> A -> A -> result) :=
  ifv (KC S v1) (fun S1 vc1 =>
    ifv (KC S1 v2) (fun S2 vc2 =>
      K S2 vc1 vc2)).

Fixpoint run_equal_partial (max_depth : nat) (conv_number conv_primitive : state -> value -> result) S v1 v2 : result :=
  let checkTypesThen S0 v1 v2 (K : type -> type -> result) :=
    let T1 := type_of v1 in
    let T2 := type_of v2 in
    ifb T1 = T2 then
      out_ter S0 (equality_test_for_same_type T1 v1 v2) : result
    else K T1 T2 in
  checkTypesThen S v1 v2 (fun T1 T2 =>
    let dc_conv v1 F v2 :=
      if_value (F S v2) (fun S0 v2' =>
        match max_depth with
        | O => arbitrary
        | S max_depth' => run_equal_partial max_depth' conv_number conv_primitive S0 v1 v2'
        end) in
    let so b :=
      out_ter S b in
    ifb (T1 = type_null \/ T1 = type_undef) /\ (T2 = type_null \/ T2 = type_undef) then
      so true
    else ifb T1 = type_number /\ T2 = type_string then
      dc_conv v1 conv_number v2
    else ifb T1 = type_string /\ T2 = type_number then
      dc_conv v2 conv_number v1
    else ifb T1 = type_bool then
      dc_conv v2 conv_number v1
    else ifb T2 = type_bool then
      dc_conv v1 conv_number v2
    else ifb (T1 = type_string \/ T1 = type_number) /\ T2 = type_object then
      dc_conv v1 conv_primitive v2
    else ifb T1 = type_object /\ (T2 = type_string \/ T2 = type_number) then
      dc_conv v2 conv_primitive v1
    else so false).

Definition run_equal :=
  run_equal_partial 4%nat (*
    If I'm not mistaking, the longest conversion chain is given by the following one:
     - string, object;
     - string, boolean;
     - string, number;
     - number, number.
  *).

Definition run_binary_op (max_step : nat) (run_call' : run_call_type) S C (op : binary_op) v1 v2 : result :=
  (* TODO: move these as definitions outside the body *)
  let conv_primitive S v :=
    to_primitive run_call' S C v None in
  let convert_twice_primitive :=
    convert_twice if_primitive conv_primitive in
  let conv_number S v :=
    to_number run_call' S C v in
  let convert_twice_number :=
    convert_twice if_number conv_number in
  let conv_string S v :=
    to_string run_call' S C v in
  let convert_twice_string :=
    convert_twice if_string conv_string in
  match op with

  | binary_op_add =>
    convert_twice_primitive S v1 v2 (fun S1 w1 w2 =>
      ifb type_of w1 = type_string \/ type_of w2 = type_string then
        convert_twice_string S1 w1 w2 (fun S2 s1 s2 =>
          out_ter S2 (s1 ++ s2))
        else
          convert_twice_number S1 w1 w2 (fun S2 n1 n2 =>
            out_ter S2 (JsNumber.add n1 n2)))

  | binary_op_mult | binary_op_div | binary_op_mod | binary_op_sub =>
    let mop := get_puremath_op op in
    convert_twice_number S v1 v2 (fun S1 n1 n2 =>
      out_ter S1 (mop n1 n2))

  | binary_op_and | binary_op_or => result_stuck (* Lazy operators are already dealt with at this point. *)

  | binary_op_left_shift | binary_op_right_shift | binary_op_unsigned_right_shift =>
    let (b_unsigned, F) := get_shift_op op in
    (if b_unsigned then to_uint32 else to_int32) run_call' S C v1 (fun S1 k1 =>
      to_uint32 run_call' S1 C v2 (fun S2 k2 =>
        let k2' := JsNumber.modulo_32 k2 in
        out_ter S2 (JsNumber.of_int (F k1 k2'))))

  | binary_op_bitwise_and | binary_op_bitwise_or | binary_op_bitwise_xor =>
    to_int32 run_call' S C v1 (fun S1 k1 =>
      to_int32 run_call' S1 C v2 (fun S2 k2 =>
        out_ter S2 (JsNumber.of_int (get_bitwise_op op k1 k2))))

  | binary_op_lt | binary_op_gt | binary_op_le | binary_op_ge =>
    let (b_swap, b_neg) := get_inequality_op op in
    convert_twice_primitive S v1 v2 (fun S1 w1 w2 =>
      let (wa, wb) := if b_swap then (w2, w1) else (w1, w2) in
      let wr := inequality_test_primitive wa wb in
      out_ter S1 (ifb wr = prim_undef then false
        else ifb b_neg = true /\ wr = true then false
        else wr))

  | binary_op_instanceof =>
    match v2 with
    | value_object l =>
      morph_option (fun _ => out_type_error S : result)
      (fun has_instance_id _ =>
        run_spec_object_has_instance max_step has_instance_id S l v1)
      (run_object_has_instance S l) tt
    | _ => out_type_error S
    end

  | binary_op_in =>
    match v2 with
    | value_object l =>
      if_string (to_string run_call' S C v1) (fun S2 x =>
        out_ter S2 (object_has_prop S2 l x))
    | _ => out_type_error S
    end

  | binary_op_equal | binary_op_disequal =>
    let finalPass b :=
      match op with
      | binary_op_equal => b
      | binary_op_disequal => negb b
      | _ => arbitrary
      end in
    if_success_bool (run_equal conv_number conv_primitive S v1 v2)
      (fun S0 => out_ter S0 (finalPass true))
      (fun S0 => out_ter S0 (finalPass false))

  | binary_op_strict_equal =>
    out_ter S (strict_equality_test v1 v2)

  | binary_op_strict_disequal =>
    out_ter S (negb (strict_equality_test v1 v2))

  | binary_op_coma =>
    out_ter S v2

  end.

Definition run_prepost_op (op : unary_op) : (number -> number) * bool :=
  match op with
  | unary_op_pre_incr => (add_one, true)
  | unary_op_pre_decr => (sub_one, true)
  | unary_op_post_incr => (add_one, false)
  | unary_op_post_decr => (sub_one, false)
  | _ => arbitrary
  end.

Definition object_delete S l x str : result :=
  let B := run_object_method object_delete_ S l in
  match run_object_get_own_property S l x with
  | full_descriptor_undef => out_ter S true
  | full_descriptor_some A =>
    if attributes_configurable A then
      out_ter (pick (object_rem_property S l x)) true
    else
      out_error_or_cst S str builtin_type_error false
  end.


Definition run_unary_op (run_expr' : run_expr_type) (run_call' : run_call_type) S C (op : unary_op) e : result :=
  ifb prepost_unary_op op then
    if_success (run_expr' S C e) (fun S1 rv1 =>
      if_success_value (out_ter S1 rv1) (fun S2 v2 =>
        if_number (to_number run_call' S2 C v2) (fun S3 n1 =>
          let (number_op, is_pre) := run_prepost_op op in
          let n2 := number_op n1 in
          let v := prim_number (if is_pre then n2 else n1) in
          if_success (ref_put_value run_call' S3 C rv1 n2) (fun S4 rv2 =>
            out_ter S4 v))))
  else
    match op with

    | unary_op_delete =>
      if_success (run_expr' S C e) (fun S1 rv =>
        match rv with
        | resvalue_value v => out_ter S1 true
        | resvalue_empty => result_stuck
        | resvalue_ref r =>
          ifb ref_is_unresolvable r then
            out_ter S1 true
          else
            match ref_base r with
            | ref_base_type_value v =>
              if_object (to_object S1 v) (fun S2 l =>
                object_delete S2 l (ref_name r) (ref_strict r))
            | ref_base_type_env_loc L =>
              env_record_delete_binding S1 L (ref_name r)
            end
        end)

    | unary_op_typeof =>
      if_success (run_expr' S C e) (fun S1 rv =>
        match rv with
        | resvalue_value v =>
          out_ter S1 (typeof_value S1 v)
        | resvalue_ref r =>
          ifb ref_is_unresolvable r then
            out_ter S1 "undefined"
          else
            if_success_value (out_ter S1 r) (fun S2 v =>
              out_ter S2 (typeof_value S2 v))
        | resvalue_empty => result_stuck
        end)

    | _ => (* Regular operators *)
      if_success_value (run_expr' S C e) (fun S1 v =>
        match op with

        | unary_op_void => out_ter S1 undef

        | unary_op_add => to_number run_call' S1 C v

        | unary_op_neg =>
          if_number (to_number run_call' S1 C v) (fun S2 n =>
            out_ter S2 (JsNumber.neg n))

        | unary_op_bitwise_not =>
          arbitrary (* TODO *)

        | unary_op_not =>
          out_ter S (neg (convert_value_to_boolean v))

        | _ => arbitrary

        end)

    end.

End Operators.


Section Interpreter.

(**************************************************************)
(** Some special cases *)

Fixpoint init_object (run_expr' : run_expr_type) S C l (pds : propdefs) : result :=
  let create_new_function_in S0 args bd :=
  creating_function_object S0 C args bd (execution_ctx_lexical_env C) (execution_ctx_strict C) in
  match pds with
  | nil => out_ter S l
  | (pn, pb) :: pds' =>
    let x := string_of_propname pn in
    let follows S1 A :=
      if_success (object_define_own_prop S1 l x A false) (fun S2 rv =>
        init_object run_expr' S2 C l pds') in
    match pb with
    | propbody_val e0 =>
      if_success_value (run_expr' S C e0) (fun S1 v0 =>
        let A := attributes_data_intro v0 true true true in
        follows S1 A)
    | propbody_get bd =>
      if_value (create_new_function_in S nil bd) (fun S1 v0 =>
        let A := attributes_accessor_intro undef v0 true true in
        follows S1 A)
    | propbody_set args bd =>
      if_value (create_new_function_in S args bd) (fun S1 v0 =>
        let A := attributes_accessor_intro v0 undef true true in
        follows S1 A)
    end
  end.

Fixpoint run_var_decl (run_call' : run_call_type) (run_expr' : run_expr_type) S C xeos : result :=
  match xeos with
  | nil => out_ter S res_empty
  | (x, eo) :: xeos' =>
    if_success (match eo with
      | None => out_ter S undef
      | Some e =>
        if_success_value (run_expr' S C e) (fun S1 v =>
          let ir := identifier_res S1 C x in
          if_success (ref_put_value run_call' S1 C ir v) (fun S2 rv =>
            out_ter S2 undef))
      end) (fun S1 rv =>
        run_var_decl run_call' run_expr' S1 C xeos')
  end.


(**************************************************************)
(** ** Definition of the interpreter *)

Fixpoint run_expr (max_step : nat) S C e : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    match e with

    | expr_literal i =>
      out_ter S (convert_literal_to_prim i)

    | expr_identifier x =>
      out_ter S (identifier_res S C x)

    | expr_unary_op op e =>
      run_unary_op run_expr' run_call' S C op e

    | expr_binary_op e1 op e2 =>
      match is_lazy_op op with
      | None =>
        if_success_value (run_expr' S C e1) (fun S1 v1 =>
          if_success_value (run_expr' S1 C e2) (fun S2 v2 =>
            run_binary_op max_step' run_call' S2 C op v1 v2))
      | Some b_ret =>
        if_success_value (run_expr' S C e1) (fun S1 v1 =>
          let b1 := convert_value_to_boolean v1 in
          ifb b1 = b_ret then out_ter S1 v1
          else
            if_success_value (run_expr' S1 C e2) (fun S2 v2 =>
              out_ter S2 v2))
      end

    | expr_object pds =>
      if_object (constructor_builtin S C builtin_object_new nil) (fun S1 l =>
        init_object run_expr' S1 C l pds)

    | expr_member e1 f =>
      run_expr' S C (expr_access e1 (expr_literal (literal_string f)))

    | expr_access e1 e2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if_success_value (run_expr' S C e2) (fun S2 v2 =>
          ifb v1 = prim_undef \/ v1 = prim_null then
            out_ref_error S2
          else
            if_string (to_string run_call' S2 C v2) (fun S3 x =>
              out_ter S3 (ref_create_value v1 x (execution_ctx_strict C)))))

    | expr_assign e1 opo e2 =>
      if_success (run_expr' S C e1) (fun S1 rv1 =>
        let follow S rv' :=
          match rv' with
          | resvalue_value v =>
            if_success (ref_put_value run_call' S C rv1 v) (fun S' rv2 =>
             out_ter S' v)
          | _ => result_stuck
          end in
        match opo with
        | None =>
          if_success_value (run_expr' S1 C e2) follow
        | Some op =>
          if_success_value (out_ter S1 rv1) (fun S2 v1 =>
            if_success_value (run_expr' S2 C e2) (fun S3 v2 =>
              if_success (run_binary_op max_step' run_call' S3 C op v1 v2) follow))
        end)

    | expr_function None args bd =>
      creating_function_object S C args bd (execution_ctx_lexical_env C) (funcbody_is_strict bd)

    | expr_function (Some fn) args bd =>
      let (lex', S') := lexical_env_alloc_decl S (execution_ctx_lexical_env C) in
      let follow L :=
        let E := pick (env_record_binds S' L) in
        if_success (env_record_create_immutable_binding S' L fn) (fun S1 rv1 =>
          if_object (creating_function_object S1 C args bd lex' (funcbody_is_strict bd)) (fun S2 l =>
            if_success (env_record_initialize_immutable_binding S2 L fn l) (fun S3 rv2 =>
              out_ter S3 l))) in
      map_nth (fun _ : unit => arbitrary) (fun L _ => follow L) 0 lex' tt

    | expr_call e1 e2s =>
      if_success (run_expr' S C e1) (fun S1 rv =>
        if_success_value (out_ter S1 rv) (fun S2 f =>
          run_list_expr run_expr' S2 C nil e2s (fun S3 args =>
            match f with
            | value_object l =>
              ifb ~ (is_callable S3 l) then out_type_error S3
              else
                let follow v :=
                  let B := extract_from_option (run_object_call S3 l) in
                  run_call' S3 C B (Some l) (Some v) args in
                match rv with
                | resvalue_value v => follow undef
                | resvalue_ref r =>
                  match ref_base r with
                  | ref_base_type_value v =>
                    ifb ref_is_property r then follow v
                    else result_stuck
                  | ref_base_type_env_loc L =>
                    follow (env_record_implicit_this_value S3 L)
                  end
                | _ => result_stuck
                end
            | _ => out_type_error S3
            end)))

    | expr_this =>
      out_ter S (execution_ctx_this_binding C)

    | expr_new e1 le2 =>
      arbitrary
      (* TODO
      (* Evaluate constructor *)
      if_success_state (run_expr' h0 s e1) (fun h1 r1 =>
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
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        let b1 := convert_value_to_boolean v1 in
        if_success_value (run_expr' S1 C (if b1 then e2 else e3)) (fun S2 v2 =>
          out_ter S2 v2))

    end
  end

(**************************************************************)

with run_stat (max_step : nat) S C t : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    let run_block' := run_block max_step' in
    match t with

    | stat_expr e =>
      run_expr' S C e

    | stat_var_decl xeos =>
      (* run_var_decl run_call' run_expr' S C xeos *) arbitrary (* As variables are not declared in [run_prog], I prefer raise an exception when such a variable should have been defined. *) (* TODO: Remove the [arbitrary] as soon as [run_prog] is correct. *)

    | stat_block ts =>
      run_block' S C resvalue_empty ts

    | stat_label l t =>
      arbitrary (* TODO *)

    | stat_with e1 t2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if_success (to_object S1 v1) (fun S2 rv2 =>
          match rv2 with
          | value_object l =>
            let lex := execution_ctx_lexical_env C in
            let (lex', S3) := lexical_env_alloc_object S2 lex l provide_this_true in
            let C' := execution_ctx_with_lex_this C lex' l in
            run_stat' S3 C' t2
          | _ => result_stuck
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
            out_ter S resvalue_empty
          end)

    | stat_do_while ls t1 e2 =>
      arbitrary (* TODO *)

    | stat_while ls e1 t2 =>
      if_success_value (run_expr' S C e1) (fun S1 v1 =>
        if (convert_value_to_boolean v1) then
          if_success_or_break (run_stat' S1 C t2) (fun S2 rv2 =>
            if_success_while rv2 (run_stat' S2 C (stat_while ls e1 t2)) (fun S3 rv3 =>
              out_ter S3 rv3))
          (fun S2 R2 =>
              ifb res_label_in R2 ls then
                out_ter S2 resvalue_empty
              else out_ter S2 (res_throw resvalue_empty)
            )
        else
          out_ter S1 undef)

    | stat_throw e =>
      if_success_value (run_expr' S C e) (fun S1 v1 =>
        out_ter S (res_throw v1))

    | stat_try t1 t2o t3o =>
      let finally : result -> result :=
        match t3o with
        | None => fun res => res
        | Some t3 => fun res =>
          match res with
          | out_ter S1 R =>
            if_success (run_stat' S1 C t3) (fun S2 rv' =>
              out_ter S2 R)
          | _ => res (* stuck or bottom *)
          end
        end
      in
      if_success_or_throw (run_stat' S C t1) (fun S1 rv1 =>
        finally (out_ter S1 rv1)) (fun S1 v =>
        match t2o with
        | None => finally (out_ter S1 (res_throw v))
        | Some (x, t2) =>
          let lex := execution_ctx_lexical_env C in
          let (lex', S') := lexical_env_alloc_decl S lex in
          match lex' with
          | L :: oldlex =>
            if_success
            (env_record_create_set_mutable_binding run_call' S C L x None v throw_irrelevant)
            (fun S2 rv2 =>
              match rv2 with
              | prim_undef =>
                let C' := execution_ctx_with_lex C lex' in
                finally (run_stat' S2 C' t2)
              | _ => result_stuck
              end)
          | nil => result_stuck
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

    | stat_for_in ls e1 e2 s =>
      arbitrary (* TODO *)

    | stat_for_in_var ls x e1o e2 s =>
      arbitrary (* TODO *)

    | stat_debugger =>
      out_ter S res_empty

    end
  end

with run_prog (max_step : nat) S C p : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_elements' := run_elements max_step' in
    match p with

    | prog_intro str els =>
      let C' := execution_ctx_initial str (* TODO:  Declare functions and variables *) in
      run_elements' S C' resvalue_empty els

    end
  end

with run_elements (max_step : nat) S C rv (els : list element) : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_stat' := run_stat max_step' in
    let run_elements' := run_elements max_step' in
    match els with

    | nil => out_ter S rv

    | element_stat t :: els' =>
      if_success_state rv (run_stat' S C t) (fun S1 rv1 =>
        run_elements' S1 C rv1 els')

    | element_func_decl name args bd :: els' =>
      (* run_elements' S C rv els' *) arbitrary (* As functions are not declared in [run_prog], I prefer raise an exception when such a function should have been defined. *) (* TODO: Remove the [arbitrary] as soon as [run_prog] is correct. *)

    end
  end

with run_call (max_step : nat) S C B (lfo : option object_loc) (vo : option value) (args : list value) : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    match B with

    | builtin_spec_op_function_call =>
      let lf := extract_from_option lfo in
      let this := extract_from_option vo in
      execution_ctx_function_call run_call' S C lf this args (fun S1 C1 =>
        if run_object_code_empty S1 lf then
          out_ter S1 (res_normal undef)
        else (
          let p := run_object_code S1 lf in
          if_success_or_return (run_prog' S1 C1 (funcbody_prog p)) (fun S2 rv =>
            out_ter S2 (res_normal undef)) (fun S2 v =>
            out_ter S2 (res_normal v))))

    | builtin_spec_op_function_bind_call =>
      arbitrary (* TODO *)

    (* call builtin *)

    | builtin_global_is_nan =>
      let v := get_arg 0 args in
      if_number (to_number run_call' S C v) (fun S0 n =>
        out_ter S0 (neg (decide (n = JsNumber.nan))))

    | builtin_global_is_finite =>
      let v := get_arg 0 args in
      if_number (to_number run_call' S C v) (fun S0 n =>
        out_ter S0 (neg (decide (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity))))

    | builtin_object_get_prototype_of =>
      let v := get_arg 0 args in
      ifb type_of v <> type_object then
        result_stuck
      else
        out_ter S (resvalue_ref (ref_create_value v "prototype" false))

    | builtin_object_get_prototype_of_call =>
      let v := get_arg 0 args in
        match v with
        | value_object l =>
          out_ter S (run_object_proto S l)
        | _ => out_type_error S
        end

    | builtin_object_proto_to_string =>
      let v := execution_ctx_this_binding C in
      match v with
      | undef => out_ter S "[object Undefined]"
      | null => out_ter S "[object Null]"
      | _ =>
        if_object (to_object S v) (fun S1 l =>
          let s := run_object_class S l in
          out_ter S1 ("[object " ++ s ++ "]"))
      end

    | builtin_object_proto_is_prototype_of =>
      let v := get_arg 0 args in
      match v with
      | value_prim w => out_ter S false
      | value_object l =>
        let vt := execution_ctx_this_binding C in
        if_object (to_object S vt) (fun S1 lo =>
          run_object_proto_is_prototype_of S1 lo l)
      end

    | builtin_bool_call =>
      let v := get_arg 0 args in
      let b := convert_value_to_boolean v in
      let O1 := object_new builtin_bool_proto "Boolean" in
      let O := object_with_primitive_value O1 b in
      let (l, S') := object_alloc S O in
      out_ter S' l

    | builtin_bool_proto_to_string_call =>
      let follow b S :=
        out_ter S (convert_bool_to_string b) in
      if_success_bool (bool_proto_value_of_call S C)
        (follow true) (follow false)

    | builtin_bool_proto_value_of_call =>
      bool_proto_value_of_call S C

    | _ =>
      arbitrary (* TODO *)

    end
  end

with run_block (max_step : nat) S C rv ts : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_block' := run_block max_step' in
    let run_stat' := run_stat max_step' in
    match ts with
    | nil => out_ter S rv
    | t :: ts' =>

      if_success_state rv (run_stat' S C t) (fun S1 rv1 =>
        run_block' S1 C rv1 ts')

    end
  end.

End Interpreter.

