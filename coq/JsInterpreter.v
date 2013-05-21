Set Implicit Arguments.
Require Import Shared.
Require Import LibFix.
Require Import JsSyntax JsSyntaxAux JsSyntaxInfos JsPreliminary JsPreliminaryAux JsInit.


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


Implicit Type Z : Type.


(**************************************************************)
(** ** Structure of This File *)
(* Definitions of the datatypes used.
 * Monadic constructors.
 * Functions corresponding to the [spec_*] of the semantics.
 * Operatorshandling.
 * Functions corresponding to syntax cases of the semantics (while, if, ...)
 * Final fixed point. *)


(**************************************************************)
(** ** Some functions to be implemented (or extracted differently). *)

Parameter JsNumber_to_int : JsNumber.number -> (* option? *) int.
(* It should never return an option, but its result will be a pain to be used... -- Martin *)


(**************************************************************)
(** ** Some types used by the interpreter *)

Inductive result :=
  | result_out : out -> result
  | result_stuck
  | result_bottom.

(* In the semantics, some rules returns an [out] which actually never
  carry a result, only an [out_void] of something (or an error).  The
  following type is there to differentiate those functions from the
  others. *)

Definition result_void := result.

(* Coercion *)

Coercion result_out : out >-> result.

(* Inhabited *)

Global Instance result_inhab : Inhab result.
Proof. applys prove_Inhab result_stuck. Qed.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section InterpreterEliminations.

(**************************************************************)
(** Generic constructions *)

Definition get_arg := get_nth undef.

Definition destr_list {A B : Type} (l : list A) (d : B) f :=
  match l with
  | nil => d
  | cons a _ => f a
  end.


(**************************************************************)
(** Error Handling *)

(** [out_error_or_cst S str B R] throws the builtin B if
    [str] is true, the value [R] otherwise. *)

Definition out_error_or_cst S str B R :=
  if str then out_ter S (res_throw B)
  else out_ter S R.

(** [out_error_or_cst S str B R] throws the builtin B if
    [str] is true, empty otherwise. *)

Definition out_error_or_void S str B :=
  if str then out_ter S (res_throw B)
  else out_void S.

Definition run_error S (B : prealloc) : result :=
  match B with
  | prealloc_syntax_error => arbitrary (* TODO:  Waiting for specification *)
  | prealloc_type_error => arbitrary (* TODO:  Waiting for specification *)
  | prealloc_ref_error => arbitrary (* TODO:  Waiting for specification *)
  | prealloc_range_error => arbitrary (* TODO:  Waiting for specification *)
  | prealloc_throw_type_error => arbitrary (* TODO:  Waiting for specification *)
  | _ => result_stuck
  end.


(**************************************************************)
(** Monadic Constructors *)

Definition if_bool_option (A : Type) (d : A) (bo : option bool) (K1 : unit -> A) (K2 : unit -> A) : A :=
  morph_option d (fun b =>
    if b then K1 tt else K2 tt) bo.
  (* todo: use an explicit "match" here, it will be easier for people to make sense of the definition *)

Definition if_bool_option_result := if_bool_option result_stuck.

Definition if_some {A : Type} (op : option A) (K : A -> result) : result :=
  morph_option result_stuck K op.
  (* todo: use an explicit "match" here, it will be easier for people to make sense of the definition *)

Definition if_ter (o : result) (K : state -> res -> result) : result :=
  match o with
  | out_ter S0 R =>
      K S0 R
  | _ => o
  end.

Definition if_success_state rv (o : result) (K : state -> resvalue -> result) : result :=
  if_ter o (fun S0 R =>
    match res_type R with
    | restype_normal =>
        K S0 (res_value (res_overwrite_value_if_empty rv R))
    | restype_throw => o
    | _ =>
        out_ter S0 (res_overwrite_value_if_empty rv R)
    end).

Definition if_success := if_success_state resvalue_empty.

Definition if_void (o : result_void) (K : state -> result) : result :=
  if_success o (fun S rv =>
    match rv with
    | resvalue_empty => K S
    | _ => result_stuck
    end).

Definition if_not_throw (o : result) (K : state -> res -> result) : result :=
  if_ter o (fun S0 R =>
    match res_type R with
    | restype_throw => o
    | _ =>
        K S0 R
    end).

Definition if_any_or_throw (o : result) (K1 : result -> result) (K2 : state -> value -> result) : result :=
  if_ter o (fun S R =>
    match res_type R with
    | restype_throw =>
      match res_value R with
      | resvalue_value v => K2 S v
      | _ => result_stuck
      end
    | _ => K1 o
    end).

Definition if_success_or_return (o : result) (K1 : state -> result) (K2 : state -> resvalue -> result) : result :=
  if_ter o (fun S R =>
    match res_type R with
    | restype_normal => K1 S
    | restype_return => K2 S (res_value R)
    | _ => o
    end).

Definition if_normal_continue_or_break (o : result) (search_label : res -> bool)
  (K1 : state -> res -> result) (K2 : state -> res -> result) : result :=
  if_ter o (fun S R =>
    let K :=
      match res_type R with
      | restype_break =>
          if search_label R then K2 else out_ter
      | restype_continue =>
          if search_label R then K1 else out_ter
      | restype_normal => K1
      | _ => out_ter
      end in
    K S R).

Definition if_break (o : result) (K : state -> res -> result) : result :=
  if_ter o (fun S R =>
    let default := out_ter S R in
    match res_type R with
    | restype_break => K S R
    | _ => default
    end).

Definition if_value (o : result) (K : state -> value -> result) : result :=
  if_success o (fun S rv =>
    match rv with
    | resvalue_value v => K S v
    | _ => result_stuck
    end).

Definition if_bool (o : result) (K : state -> bool -> result) : result :=
  if_value o (fun S v =>
    match v with
    | prim_bool b => K S b
    | _ => result_stuck
    end).

Definition if_success_bool (o : result) (K1 K2 : state -> result) : result :=
  if_bool o (fun S b =>
    let K := if b then K1 else K2 in
    K S).

Definition if_success_primitive (o : result) (K : state -> prim -> result) : result :=
  if_value o (fun S v =>
    match v with
    | value_prim w => K S w
    | value_object _ => result_stuck
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
    | value_prim _ => result_stuck
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
    | value_object _ => result_stuck
    end).

End InterpreterEliminations.

Section LexicalEnvironments.


(**************************************************************)
(** Operations on objects *)

Definition run_object_method Z (Proj : object -> Z) S l : Z :=
  Proj (pick (object_binds S l)).

Definition run_object_code_empty S l : bool :=
  morph_option true (fun _ => false)
    (object_code_ (pick (object_binds S l))).

Definition run_object_heap_set_properties S l P' : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_with_properties O P').

(* todo: move elsewhere : *)
Global Instance object_properties_keys_as_list_pickable : forall S l,
  Pickable (object_properties_keys_as_list S l).
Proof.
  introv. applys pickable_make
    (List.map fst (Heap.to_list (run_object_method object_properties_ S l))).
  introv [xs Hxs]. lets (P&HP&C): (rm Hxs). exists P. splits~.
  skip. (* Needs properties about [heap_keys_as_list]. *)
Qed.

Definition run_object_heap_set_extensible b S l : state :=
  let O := pick (object_binds S l) in
  object_write S l (object_set_extensible O b).


(**************************************************************)
(* The functions taking such arguments can call any arbitrary code,
   i.e. can also call arbitrary pogram and expression.  They thus need
   a pointer to the main functions.  Those types are just the ones of
   those main functions. *)

Record runs_type : Type := runs_type_intro {
    runs_type_expr : state -> execution_ctx -> expr -> result;
    runs_type_stat : state -> execution_ctx -> stat -> result;
    runs_type_prog : state -> execution_ctx -> prog -> result;
    runs_type_call : state -> execution_ctx -> prealloc -> list value -> result;
    runs_type_call_full : state -> execution_ctx -> object_loc -> value -> list value -> result
  }.

Implicit Type runs : runs_type.


(**************************************************************)
(** Operations on environments *)

Definition run_decl_env_record_binds_value Ed x : value :=
  snd (pick (Heap.binds Ed x)).

Definition run_object_get_own_prop S l x : option full_descriptor :=
  match run_object_method object_get_own_prop_ S l with
  | builtin_get_own_prop_default =>
    let P := run_object_method object_properties_ S l in
    (* todo: serait-il judicieux de définir un if_def_full_descriptor pour matcher les full-descriptors?
       même si c'est juste un alias pour morph_option, ça serait plus lisible. *)
    morph_option (Some full_descriptor_undef)
      (fun A => Some (A : full_descriptor))
      (Heap.read_option P x)
  | builtin_get_own_prop_args_obj => 
    arbitrary (* TODO:  Waiting for the specification *)
  end.

Definition object_get_prop_body run_object_get_prop S v x : option full_descriptor :=
  match v with
  | value_prim w =>
      ifb v = null then Some full_descriptor_undef else None
  | value_object l =>
    morph_option None (fun D =>
        ifb D = full_descriptor_undef then (
          let lproto := run_object_method object_proto_ S l in
          run_object_get_prop S lproto x
        ) else Some D)
        (run_object_get_own_prop S l x)
  end.

Definition run_object_get_prop := FixFun3 object_get_prop_body.

Definition object_has_prop S l x : option bool :=
  option_map (fun D =>
    decide (D <> full_descriptor_undef))
    (run_object_get_prop S l x).

Definition object_proto_is_prototype_of_body run_object_proto_is_prototype_of S l0 l : result :=
  match run_object_method object_proto_ S l with
  | null => out_ter S false
  | value_object l' =>
      ifb l' = l0
        then out_ter S true
        else run_object_proto_is_prototype_of S l0 l'
  | value_prim _ => result_stuck
  end.

Definition run_object_proto_is_prototype_of :=
  FixFun3 object_proto_is_prototype_of_body.

Definition env_record_lookup Z (d : Z) S L (K : env_record -> Z) : Z :=
  morph_option d K (Heap.read_option (state_env_record_heap S) L).

Definition env_record_has_binding S L x : option bool :=
  env_record_lookup (fun _ : unit => None) S L (fun E _ =>
    match E with
    | env_record_decl Ed =>
        Some (decide (decl_env_record_indom Ed x))
    | env_record_object l pt =>
        object_has_prop S l x
    end) tt.

Fixpoint lexical_env_get_identifier_ref S X x str : option ref :=
  match X with
  | nil =>
      Some (ref_create_value undef x str)
  | L :: X' =>
      if_bool_option None (env_record_has_binding S L x) (fun _ =>
        Some (ref_create_env_loc L x str)) (fun _ =>
        lexical_env_get_identifier_ref S X' x str)
  end.

Definition env_record_delete_binding S L x : result :=
  env_record_lookup (fun _ : unit => result_stuck) S L (fun E _ =>
    match E return result with
    | env_record_decl Ed =>
      match Heap.read_option Ed x with
      | None =>
          out_ter S true
      | Some (mutability_nondeletable, v) =>
          out_ter S false
      | Some (mu, v) =>
          out_ter (state_with_env_record_heap S
            (Heap.write (state_env_record_heap S) L
              (env_record_decl (Heap.rem Ed x)))) true
      end
    | env_record_object l pt =>
        result_stuck
    end) tt.

Definition identifier_res S C x :=
  let X := execution_ctx_lexical_env C in
  let str := execution_ctx_strict C in
  lexical_env_get_identifier_ref S X x str.

Definition object_get_builtin runs B S C vthis l x : result := (* Corresponds to the construction [spec_object_get_1] of the specification. *)
  match B with
  | builtin_get_default =>
    if_some (run_object_get_prop S l x) (fun D =>
      match D with
      | full_descriptor_undef => out_ter S undef
      | attributes_data_of Ad =>
          out_ter S (attributes_data_value Ad)
      | attributes_accessor_of Aa =>
          match attributes_accessor_get Aa with
          | undef => out_ter S undef
          | value_object lf =>
              match vthis with
              | value_object lthis =>
                  runs_type_call_full runs S C lf lthis nil
              | value_prim _ => result_stuck
              end
          | value_prim _ => (* TODO:  Waiting for the specification. *)
              result_stuck
          end
      end)
  | builtin_get_function =>
    result_stuck (* TODO:  Waiting for the specification *)
  | builtin_get_args_obj => 
    result_stuck (* TODO:  Waiting for the specification *)
  end.

Definition object_get runs S C v x : result := (* This [v] should be a location. *)
  match v with
  | value_object l =>
      let B := run_object_method object_get_ S l in
      object_get_builtin runs B S C l l x
  | value_prim _ => result_stuck
  end.


(**************************************************************)
(** Conversions *)

Definition prim_new_object S w : result :=
  arbitrary (* TODO:  Waiting for the specification *).

Definition to_object S v : result :=
  match v with
  | prim_null | prim_undef => run_error S prealloc_type_error
  | value_prim w => prim_new_object S w
  | value_object l => out_ter S l
  end.

Definition prim_value_get runs S C v x : result :=
  if_object (to_object S v) (fun S' l =>
    object_get_builtin runs builtin_get_default S' C v l x).

Definition run_value_viewable_as_prim s S v : option prim :=
  match v with
  | value_prim w => Some w
  | value_object l =>
      let s := run_object_method object_class_ S l in
      match run_object_method object_prim_value_ S l with
      | Some (value_prim w) => Some w
      | _ => None
      end
  end.


(**************************************************************)

Definition env_record_get_binding_value runs S C L x str : result :=
  env_record_lookup result_stuck S L (fun er =>
    match er with
    | env_record_decl Ed =>
      if_some (Heap.read_option Ed x) (fun rm =>
        let (mu, v) := rm in (* Martin: on fait "let '(a,b)" sur les paires, ça aide le typeur *)
        ifb mu = mutability_uninitialized_immutable then
          out_error_or_cst S str prealloc_ref_error undef
        else out_ter S v)
    | env_record_object l pt =>
      if_bool_option_result (object_has_prop S l x) (fun _ =>
        object_get runs S C l x) (fun _ =>
        out_error_or_cst S str prealloc_ref_error undef)
    end).

Definition object_can_put S l x : option bool :=
  match run_object_method object_can_put_ S l with

  | builtin_can_put_default =>
    morph_option None (fun D =>
      match D with
      | attributes_accessor_of Aa =>
        Some (decide (attributes_accessor_set Aa <> undef))
      | attributes_data_of Ad =>
        Some (attributes_data_writable Ad)
      | full_descriptor_undef =>
        match run_object_method object_proto_ S l with
        | null =>
          Some (run_object_method object_extensible_ S l)
        | value_object lproto =>
          option_map (fun D' =>
            match D' with
            | full_descriptor_undef =>
              run_object_method object_extensible_ S l
            | attributes_accessor_of Aa =>
              decide (attributes_accessor_set Aa <> undef)
            | attributes_data_of Ad =>
              if run_object_method object_extensible_ S l then
                attributes_data_writable Ad
              else false
          end) (run_object_get_prop S lproto x)
        | value_prim _ => None
        end
      end) (run_object_get_own_prop S l x)

  end.

Definition object_define_own_prop S l x Desc str : result :=
  let B := run_object_method object_define_own_prop_ S l
  in match B with
  | builtin_define_own_prop_default =>
    if_some (run_object_get_own_prop S l x) (fun D =>
      let reject S :=
        out_error_or_cst S str prealloc_type_error false
      in match D, run_object_method object_extensible_ S l with
      | full_descriptor_undef, false => reject S
      | full_descriptor_undef, true =>
        let A : attributes :=
          ifb descriptor_is_generic Desc \/ descriptor_is_data Desc
          then attributes_data_of_descriptor Desc
          else attributes_accessor_of_descriptor Desc
        in let S1 := pick (object_set_property S l x A)
        in out_ter S1 true
      | full_descriptor_some A, bext =>
        let object_define_own_prop_write S A :=
          let A' := attributes_update A Desc in
          let S' := pick (object_set_property S l x A') in
          out_ter S' true
        in ifb descriptor_contains A Desc then
          out_ter S true
        else ifb attributes_change_enumerable_on_non_configurable A Desc then
          reject S
        else ifb descriptor_is_generic Desc then
          object_define_own_prop_write S A
        else ifb attributes_is_data A <> descriptor_is_data Desc then
          if neg (attributes_configurable A) then
            reject S
          else let A':=
              match A return attributes with
              | attributes_data_of Ad =>
                attributes_accessor_of_attributes_data Ad
              | attributes_accessor_of Aa =>
                attributes_data_of_attributes_accessor Aa
              end
            in let S' := pick (object_set_property S l x A')
            in object_define_own_prop_write S' A'
        else match A with
          | attributes_data_of Ad =>
            ifb attributes_change_data_on_non_configurable Ad Desc then
              reject S
            else object_define_own_prop_write S A
          | attributes_accessor_of Aa =>
            ifb attributes_change_accessor_on_non_configurable Aa Desc then
              reject S
            else object_define_own_prop_write S A
          end
      end)
    | builtin_define_own_prop_args_obj =>
      result_stuck (* TODO:  Waiting for the specification *)
  end.


(**************************************************************)

Definition ref_get_value runs S C rv : result :=
  match rv with
  | resvalue_empty => result_stuck
  | resvalue_value v => out_ter S v
  | resvalue_ref r =>
    match ref_kind_of r with
    | ref_kind_null | ref_kind_undef => run_error S prealloc_ref_error
    | ref_kind_primitive_base | ref_kind_object =>
      match ref_base r with
      | ref_base_type_value v =>
        (ifb ref_has_primitive_base r then prim_value_get
        else object_get) runs S C v (ref_name r)
      | ref_base_type_env_loc L =>
        env_record_get_binding_value runs S C L (ref_name r) (ref_strict r)
      end
    | ref_kind_env_record =>
      match ref_base r with
      | ref_base_type_value v => result_stuck
      | ref_base_type_env_loc L =>
        env_record_get_binding_value runs S C L (ref_name r) (ref_strict r)
      end
    end
  end.

Definition object_put_complete runs B S C vthis l x v str : result_void :=
  match B with

  | builtin_put_default =>
    if_some (object_can_put S l x) (fun b =>
      if b then
        if_some (run_object_get_own_prop S l x) (fun D =>
          match D with

          | attributes_data_of Ad =>
            match vthis with
            | value_object lthis =>
              let Desc := descriptor_intro (Some v) None None None None None in
              if_success (object_define_own_prop S l x Desc str) (fun S1 rv =>
                out_void S1)
            | value_prim wthis =>
              out_error_or_void S str prealloc_type_error
            end

          | _ =>
            if_some (run_object_get_prop S l x) (fun D' =>
              match D' with
              | attributes_accessor_of Aa' =>
                match attributes_accessor_set Aa' with
                | value_object lfsetter =>
                  if_success (runs_type_call_full runs S C lfsetter vthis (v::nil)) (fun S1 rv =>
                    out_void S1)
                | value_prim _ => result_stuck
                end
              | _ =>
                match vthis with
                | value_object lthis =>
                  let Desc := descriptor_intro_data v true true true in
                  if_success (object_define_own_prop S l x Desc str) (fun S1 rv =>
                    out_void S1)
                | value_prim wthis =>
                  out_error_or_void S str prealloc_type_error
                end
              end)

          end)
        else
          out_error_or_void S str prealloc_type_error)

    end.

Definition object_put runs S C l x v str : result_void :=
  let B := run_object_method object_put_ S l in
  object_put_complete runs B S C l l x v str.

Definition env_record_set_mutable_binding runs S C L x v str : result_void :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    if_some (Heap.read_option Ed x) (fun rm =>
      let (mu, v_old) := rm in
      ifb mutability_is_mutable mu then
        out_void (env_record_write_decl_env S L x mu v)
      else if str then
        run_error S prealloc_type_error
      else out_ter S prim_undef)
  | env_record_object l pt =>
    object_put runs S C l x v str
  end.

Definition prim_value_put runs S C w x v str : result_void :=
  if_object (to_object S w) (fun S1 l =>
    object_put_complete runs builtin_put_default S1 C w l x v str).

Definition ref_put_value runs S C rv v : result_void :=
  match rv with
  | resvalue_value v => run_error S prealloc_ref_error
  | resvalue_ref r =>
    ifb ref_is_unresolvable r then (
      if ref_strict r then run_error S prealloc_ref_error
      else object_put runs S C prealloc_global (ref_name r) v throw_false)
    else
      match ref_base r with
      | ref_base_type_value (value_object l) =>
        object_put runs S C l (ref_name r) v (ref_strict r)
      | ref_base_type_value (value_prim w) =>
        ifb ref_kind_of r = ref_kind_primitive_base then
          prim_value_put runs S C w (ref_name r) v (ref_strict r)
        else result_stuck
      | ref_base_type_env_loc L =>
        env_record_set_mutable_binding runs S C L (ref_name r) v (ref_strict r)
      end
  | resvalue_empty => result_stuck
  end.

Definition if_success_value runs C (o : result) (K : state -> value -> result) : result :=
  if_success o (fun S1 rv1 =>
    if_success (ref_get_value runs S1 C rv1) (fun S2 rv2 =>
      match rv2 with
      | resvalue_value v => K S2 v
      | _ => run_error S2 prealloc_ref_error
      end)).


Definition env_record_create_mutable_binding S L x (deletable_opt : option bool) : result_void :=
  let deletable := unsome_default false deletable_opt in
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    ifb decl_env_record_indom Ed x then result_stuck
    else
      let S' := env_record_write_decl_env S L x (mutability_of_bool deletable) undef in
      out_void S'
  | env_record_object l pt =>
    if_bool_option_result (object_has_prop S l x) (fun _ => result_stuck) (fun _ =>
      let A := attributes_data_intro undef true true deletable in
      if_success (object_define_own_prop S l x A throw_true) (fun S1 rv =>
        out_void S1))
  end.

Definition env_record_create_set_mutable_binding runs S C L x (deletable_opt : option bool) v str : result_void :=
  if_void (env_record_create_mutable_binding S L x deletable_opt) (fun S =>
    env_record_set_mutable_binding runs S C L x v str).

Definition env_record_create_immutable_binding S L x : result_void :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    ifb decl_env_record_indom Ed x then result_stuck
    else out_void
      (env_record_write_decl_env S L x mutability_uninitialized_immutable undef)
  | env_record_object _ _ => result_stuck
  end.

Definition env_record_initialize_immutable_binding S L x v : result_void :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed =>
    ifb pick (Heap.binds Ed x) = (mutability_uninitialized_immutable, undef) then
      let S' := env_record_write_decl_env S L x mutability_immutable v in
      out_void S'
    else result_stuck
  | env_record_object _ _ => result_stuck
  end.


(**************************************************************)
(** Conversions *)

Definition object_default_value runs S C l (prefo : option preftype) : result :=
  match run_object_method object_default_value_ S l with

  | builtin_default_value_default =>
    let gpref := unsome_default preftype_number prefo in
    let lpref := other_preftypes gpref in
    let gmeth := method_of_preftype gpref in
    let sub S' x K :=
      if_object (object_get runs S' C l x) (fun S1 lfo =>
        let lf := value_object lfo in
        match run_callable S lf with
        | Some B =>
          if_success_value runs C
            (runs_type_call_full runs S C lfo l nil) (fun S2 v =>
            match v with
            | value_prim w => out_ter S w
            | value_object l => K S2
            end)
        | None => K S1
        end) in
    sub S gmeth (fun S' =>
      let lmeth := method_of_preftype lpref in
      sub S' lmeth (fun _ => run_error S prealloc_type_error))

  end.


Definition to_primitive runs S C v (prefo : option preftype) : result :=
  match v with
  | value_prim w => out_ter S w
  | value_object l => object_default_value runs S C l prefo
  end.

Definition to_number runs S C v : result :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_number w)
  | value_object l =>
    if_success_primitive (to_primitive runs S C l (Some preftype_number)) (fun S1 w =>
      out_ter S (convert_prim_to_number w))
  end.

Definition to_integer runs S C v : result :=
  if_success (to_number runs S C v) (fun S1 rv1 =>
    match rv1 with
    | prim_number n =>
      out_ter S (convert_number_to_integer n)
    | _ => result_stuck
    end).

Definition to_int32 runs S C v (K : state -> int -> result) : result :=
  if_number (to_number runs S C v) (fun S' n =>
    K S' (JsNumber.to_int32 n)).

Definition to_uint32 runs S C v (K : state -> int -> result) : result :=
  if_number (to_number runs S C v) (fun S' n =>
    K S' (JsNumber.to_uint32 n)).

Definition to_string runs S C v : result :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_string w)
  | value_object l =>
    if_success_primitive (to_primitive runs S C l (Some preftype_string)) (fun S1 w =>
      out_ter S (convert_prim_to_string w))
  end.

Definition env_record_implicit_this_value S L : value :=
  match pick (env_record_binds S L) with
  | env_record_decl Ed => undef
  | env_record_object l provide_this =>
    if provide_this
      then l : value
      else undef
  end.


(**************************************************************)
(** Built-in constructors *)

Definition call_object_new S v : result :=
  match type_of v return result with
  | type_object => out_ter S v
  | type_string | type_bool | type_number =>
      to_object S v
  | type_null | type_undef =>
      let O := object_new prealloc_object_proto "Object" in
      let (l, S') := object_alloc S O in
      out_ter S' l
  end.

Definition bool_proto_value_of_call S C : result :=
  let v := execution_ctx_this_binding C in
  match run_value_viewable_as_prim "Boolean" S v with
  | Some (prim_bool b) => out_ter S b
  | _ => run_error S prealloc_type_error
  end.

Definition run_construct_prealloc runs B S C (args : list value) : result :=
  match B with

  | prealloc_object =>
    let v := get_arg 0 args in
    call_object_new S v

  | prealloc_function =>
    arbitrary (* TODO:  Waiting for specification *)

  | prealloc_bool =>
    let v := get_arg 0 args in
    let b := convert_value_to_boolean v in
    let O1 := object_new prealloc_bool_proto "Boolean" in
    let O := object_with_primitive_value O1 b in
    let (l, S') := object_alloc S O in
    out_ter S' l

  | prealloc_number =>
    let follow S' v :=
      let O1 := object_new prealloc_number_proto "Number" in
      let O := object_with_primitive_value O1 v in
      let (l, S1) := object_alloc S' O in
      out_ter S1 l
      in
    ifb args = nil then
      follow S JsNumber.zero
    else
      let v := get_arg 0 args in
      if_value (to_number runs S C v) follow

  | prealloc_array =>
    arbitrary (* TODO:  Waiting for specification*)

  | prealloc_string =>
    arbitrary (* TODO:  Waiting for specification *)

  | _ => result_stuck (* TODO:  Is there other cases missing? *)

  end.

Definition run_construct_default runs S C l args :=
  if_value (object_get runs S C l "prototype") (fun S1 v1 =>
    let vproto :=
      ifb type_of v1 = type_object then v1
      else prealloc_object_proto
      in
    let O := object_new vproto "Object" in
    let (l', S2) := object_alloc S1 O in
    if_value (runs_type_call_full runs S2 C l l' args) (fun S3 v2 =>
      let vr := ifb type_of v2 = type_object then v2 else l' in
      out_ter S3 vr)).

Definition run_construct runs S C l args : result :=
  if_some (run_object_method object_construct_ S l) (fun co =>
    match co with
    | construct_default =>
      run_construct_default runs S C l args
    | construct_prealloc B =>
      run_construct_prealloc runs B S C args
    | construct_after_bind =>
      result_stuck
    end).


(**************************************************************)

Definition creating_function_object_proto runs S C l : result :=
  if_object (run_construct_prealloc runs prealloc_object S C nil) (fun S1 lproto =>
    let A1 := attributes_data_intro l true false true in
    if_bool (object_define_own_prop S1 lproto "constructor" A1 false) (fun S2 b =>
      let A2 := attributes_data_intro lproto true false false in
      object_define_own_prop S2 l "prototype" A2 false)).

Definition creating_function_object runs S C (names : list string) (bd : funcbody) X str : result :=
  let O := object_create prealloc_function_proto "Function" true Heap.empty in
  let O1 := object_with_invokation O
    (Some construct_default)
    (Some call_default)
    (Some builtin_has_instance_function) in
  let O2 := object_with_details O1 (Some X) (Some names) (Some bd) None None None None in
  let (l, S1) := object_alloc S O2 in
  let A1 := attributes_data_intro (JsNumber.of_int (List.length names)) false false false in
  if_success (object_define_own_prop S1 l "length" A1 false) (fun S2 rv1 =>
    if_bool (creating_function_object_proto runs S2 C l) (fun S3 b =>
      if negb str then out_ter S3 l
      else (
        let vthrower := value_object prealloc_throw_type_error in
        let A2 := attributes_accessor_intro vthrower vthrower false false in
        if_success (object_define_own_prop S3 l "caller" A2 false) (fun S4 rv2 =>
          if_success (object_define_own_prop S4 l "arguments" A2 false) (fun S5 rv3 =>
            out_ter S5 l))))).

Fixpoint binding_inst_formal_params runs S C L (args : list value) (names : list string) str {struct names} : result_void :=
  match names with
  | nil => out_void S
  | argname :: names' =>
    let v := hd undef args in
    if_some (env_record_has_binding S L argname) (fun hb =>
      let follow S' :=
        if_void (env_record_set_mutable_binding runs S' C L argname v str) (fun S1 =>
          binding_inst_formal_params runs S1 C L (tl args) names' str)
      in if hb then follow S
      else if_void (env_record_create_mutable_binding S L argname None) follow)
  end.

Fixpoint binding_inst_function_decls runs S C L (fds : list funcdecl) str bconfig {struct fds} : result_void :=
  match fds with
  | nil => out_void S
  | fd :: fds' =>
      let fbd := funcdecl_body fd in
      let str_fd := funcbody_is_strict fbd in
      let fparams := funcdecl_parameters fd in
      let fname := funcdecl_name fd in
      if_object (creating_function_object runs S C fparams fbd (execution_ctx_variable_env C) str_fd) (fun S1 fo =>
        let follow S2 :=
          if_void (env_record_set_mutable_binding runs S2 C L fname fo str) (fun S3 =>
            binding_inst_function_decls runs S3 C L fds' str bconfig)
        in if_bool_option_result (env_record_has_binding S1 L fname) (fun _ =>
          ifb L = env_loc_global_env_record then (
            if_some (run_object_get_prop S1 prealloc_global fname) (fun D =>
              match D with
              | full_descriptor_undef => result_stuck
              | full_descriptor_some A =>
                ifb attributes_configurable A then (
                  let A' := attributes_data_intro undef true true bconfig in
                  if_void (object_define_own_prop S1 prealloc_global fname A' true)
                    follow
                ) else ifb descriptor_is_accessor A
                  \/ attributes_writable A = false \/ attributes_enumerable A = false then
                    run_error S1 prealloc_type_error
                else follow S1
              end)
          ) else follow S1) (fun _ =>
            if_void (env_record_create_mutable_binding S1 L fname (Some bconfig)) follow))
  end.

Fixpoint binding_inst_var_decls runs S C L (vds : list string) bconfig str : result_void :=
  match vds with
  | nil => out_void S
  | vd :: vds' =>
    let bivd S := binding_inst_var_decls runs S C L vds' bconfig str in
    if_bool_option_result (env_record_has_binding S L vd) (fun _ =>
      bivd S) (fun _ =>
      if_void (env_record_create_set_mutable_binding runs S C L vd (Some bconfig) undef str) (fun S1 =>
        bivd S1))
  end.

Definition create_arguments_object S C l (xs : list prop_name) (args : list value) L str : result :=
  (* LATER:  This code is only temporary for tests and does not follow the specification. *)
  let obj := object_create_builtin prealloc_object_proto "Arguments" Heap.empty in
  let (l, S') := object_alloc S obj in
  out_ter S' l.

Definition binding_inst_arg_obj runs S C lf p xs args L : result_void :=
  let arguments := "arguments" in
  let str := prog_intro_strictness p in
    if_object (create_arguments_object S C lf xs args L str) (fun S1 largs =>
      if str then
        if_void (env_record_create_immutable_binding S1 L arguments) (fun S2 =>
          env_record_initialize_immutable_binding S2 L arguments largs)
      else
        env_record_create_set_mutable_binding runs S1 C L arguments None largs false).

Definition execution_ctx_binding_inst runs S C (ct : codetype) (funco : option object_loc) p (args : list value) : result_void :=
  destr_list (execution_ctx_variable_env C) result_stuck (fun L =>
    let str := prog_intro_strictness p in
    let follow S' names :=
      let bconfig := decide (ct = codetype_eval) in
      let fds := prog_funcdecl p in
      if_void (binding_inst_function_decls runs S' C L fds str bconfig) (fun S1 =>
        if_some (env_record_has_binding S1 L "arguments") (fun bdefined =>
          let follow2 S' :=
            let vds := prog_vardecl p in
            binding_inst_var_decls runs S' C L vds str (prog_intro_strictness p)
          in match ct, funco, bdefined with
          | codetype_func, Some func, false =>
            if_void (binding_inst_arg_obj runs S1 C func p names args L) (fun S2 =>
              follow2 S2)
          | codetype_func, _, false => result_stuck
          | _, _, _ => follow2 S1
          end))
    in match ct, funco with
      | codetype_func, Some func =>
        if_some (run_object_method object_formal_parameters_ S func) (fun names =>
          if_void (binding_inst_formal_params runs S C L args names str) (fun S' =>
            follow S' names))
      | codetype_func, _ => result_stuck
      | _, None => follow S nil
      | _, _ => result_stuck
      end).


(**************************************************************)
(** Function Calls *)

Definition run_call_default runs S C (lf : object_loc) : result := (* Corresponds to the [spec_call_default_1] of the specification. *)
  let follow (o : result) :=
    if_success_or_return o
      (fun S' => out_ter S' undef) out_ter
  in let default := out_ter S undef
  in match run_object_method object_code_ S lf with
  | None => follow default
  | Some bd =>
    follow
      (ifb funcbody_empty bd then default
      else runs_type_prog runs S C (funcbody_prog bd))
  end.

Definition entering_func_code runs S C lf vthis (args : list value) : result :=
  if_some (run_object_method object_code_ S lf) (fun bd =>
    let str := funcbody_is_strict bd in
    let follow S' vthis' :=
      if_some (run_object_method object_scope_ S' lf) (fun lex =>
        let (lex', S1) := lexical_env_alloc_decl S' lex in
        let C' := execution_ctx_intro_same lex' vthis' str in
        if_void (execution_ctx_binding_inst runs S1 C' codetype_func (Some lf) (funcbody_prog bd) args) (fun S2 =>
        run_call_default runs S2 C' lf))
    in if str then follow S vthis
    else match vthis with
    | value_object lthis => follow S vthis
    | null | undef => follow S prealloc_global
    | value_prim _ => if_value (to_object S vthis) follow
    end).


(**************************************************************)

Fixpoint run_object_has_instance_loop (max_step : nat) S lv vo : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    match vo with
    | value_prim _ =>
      run_error S prealloc_type_error
    | value_object lo =>
      match run_object_method object_proto_ S lv with
      | null =>
        out_ter S false
      | value_object proto =>
        ifb proto = lo then out_ter S true
        else run_object_has_instance_loop max_step' S proto lo
      | value_prim _ =>
        result_stuck
      end
    end
  end.

Definition run_object_has_instance (max_step : nat) runs B S C l v : result :=
  match B with

  | builtin_has_instance_function =>
    match v with
    | value_prim w => out_ter S false
    | value_object lv =>
      if_value (object_get runs S C l "prototype") (fun S1 v =>
        run_object_has_instance_loop max_step S1 lv v)
    end

  | builtin_has_instance_after_bind =>
    arbitrary (* TODO:  Waiting for the specification *)

  end.


(**************************************************************)

Definition from_prop_descriptor runs S C D : result :=
  match D with
  | full_descriptor_undef => out_ter S undef
  | full_descriptor_some A =>
    if_object (run_construct_prealloc runs prealloc_object S C nil) (fun S1 l =>
      let follow S0 :=
        let A1 := attributes_data_intro_all_true (attributes_enumerable A) in
        if_void (object_define_own_prop S0 l "enumerable" (descriptor_of_attributes A1) throw_false) (fun S0' =>
          let A2 := attributes_data_intro_all_true (attributes_configurable A) in
          if_void (object_define_own_prop S0' l "configurable" (descriptor_of_attributes A2) throw_false) (fun S' =>
            out_ter S' l))
      in match A with
      | attributes_data_of Ad =>
        let A1 := attributes_data_intro_all_true (attributes_data_value Ad) in
        if_void (object_define_own_prop S1 l "value" (descriptor_of_attributes A1) throw_false) (fun S2 =>
          let A2 := attributes_data_intro_all_true (attributes_data_writable Ad) in
          if_void (object_define_own_prop S2 l "writable" (descriptor_of_attributes A2) throw_false) follow)
      | attributes_accessor_of Aa =>
        let A1 := attributes_data_intro_all_true (attributes_accessor_get Aa) in
        if_void (object_define_own_prop S1 l "get" (descriptor_of_attributes A1) throw_false) (fun S2 =>
          let A2 := attributes_data_intro_all_true (attributes_accessor_set Aa) in
          if_void (object_define_own_prop S2 l "set" (descriptor_of_attributes A2) throw_false) follow)
      end)
  end.

End LexicalEnvironments.

Implicit Type runs : runs_type.


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
        | O => result_bottom
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

Definition run_binary_op (max_step : nat) runs S C (op : binary_op) v1 v2 : result :=
  let conv_primitive S v :=
    to_primitive runs S C v None in
  let convert_twice_primitive :=
    convert_twice if_primitive conv_primitive in
  let conv_number S v :=
    to_number runs S C v in
  let convert_twice_number :=
    convert_twice if_number conv_number in
  let conv_string S v :=
    to_string runs S C v in
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
    (if b_unsigned then to_uint32 else to_int32) runs S C v1 (fun S1 k1 =>
      to_uint32 runs S1 C v2 (fun S2 k2 =>
        let k2' := JsNumber.modulo_32 k2 in
        out_ter S2 (JsNumber.of_int (F k1 k2'))))

  | binary_op_bitwise_and | binary_op_bitwise_or | binary_op_bitwise_xor =>
    to_int32 runs S C v1 (fun S1 k1 =>
      to_int32 runs S1 C v2 (fun S2 k2 =>
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
      morph_option (fun _ => run_error S prealloc_type_error : result)
      (fun has_instance_id _ =>
        run_object_has_instance max_step runs has_instance_id S C l v1)
      (run_object_method object_has_instance_ S l) tt
    | value_prim _ => run_error S prealloc_type_error
    end

  | binary_op_in =>
    match v2 with
    | value_object l =>
      if_string (to_string runs S C v1) (fun S2 x =>
        if_some (object_has_prop S2 l x) (out_ter S2))
    | value_prim _ => run_error S prealloc_type_error
    end

  | binary_op_equal | binary_op_disequal =>
    let finalPass b :=
      match op with
      | binary_op_equal => b
      | binary_op_disequal => negb b
      | _ => arbitrary
      end in
    if_bool (run_equal conv_number conv_primitive S v1 v2) (fun S0 b0 =>
      out_ter S0 (finalPass b0))

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
  if_some (run_object_get_own_prop S l x) (fun D =>
    match D with
    | full_descriptor_undef => out_ter S true
    | full_descriptor_some A =>
      if attributes_configurable A then
        out_ter (pick (object_rem_property S l x)) true
      else
        out_error_or_cst S str prealloc_type_error false
    end).

Definition run_typeof_value S v :=
  match v with
  | value_prim w => typeof_prim w
  | value_object l => ifb is_callable S l then "function" else "object"
  end.

Definition run_unary_op runs S C (op : unary_op) e : result :=
  ifb prepost_unary_op op then
    if_success (runs_type_expr runs S C e) (fun S1 rv1 =>
      if_success_value runs C (out_ter S1 rv1) (fun S2 v2 =>
        if_number (to_number runs S2 C v2) (fun S3 n1 =>
          let (number_op, is_pre) := run_prepost_op op in
          let n2 := number_op n1 in
          let v := prim_number (if is_pre then n2 else n1) in
          if_void (ref_put_value runs S3 C rv1 n2) (fun S4 =>
            out_ter S4 v))))
  else
    match op with

    | unary_op_delete =>
      if_success (runs_type_expr runs S C e) (fun S1 rv =>
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
      if_success (runs_type_expr runs S C e) (fun S1 rv =>
        match rv with
        | resvalue_value v =>
          out_ter S1 (run_typeof_value S1 v)
        | resvalue_ref r =>
          ifb ref_is_unresolvable r then
            out_ter S1 "undefined"
          else
            if_success_value runs C (out_ter S1 r) (fun S2 v =>
              out_ter S2 (run_typeof_value S2 v))
        | resvalue_empty => result_stuck
        end)

    | _ => (* Regular operators *)
      if_success_value runs C (runs_type_expr runs S C e) (fun S1 v =>
        match op with

        | unary_op_void => out_ter S1 undef

        | unary_op_add => to_number runs S1 C v

        | unary_op_neg =>
          if_number (to_number runs S1 C v) (fun S2 n =>
            out_ter S2 (JsNumber.neg n))

        | unary_op_bitwise_not =>
          to_int32 runs S1 C v (fun S2 k =>
            out_ter S2 (JsNumber.of_int (JsNumber.int32_bitwise_not k)))

        | unary_op_not =>
          out_ter S (neg (convert_value_to_boolean v))

        | _ => result_stuck

        end)

    end.

End Operators.


Section Interpreter.

(**************************************************************)
(** Some special cases *)

Fixpoint init_object runs S C l (pds : propdefs) : result :=
  let create_new_function_in S0 args bd :=
  creating_function_object runs S0 C args bd (execution_ctx_lexical_env C) (execution_ctx_strict C) in
  match pds with
  | nil => out_ter S l
  | (pn, pb) :: pds' =>
    let x := string_of_propname pn in
    let follows S1 A :=
      if_success (object_define_own_prop S1 l x A false) (fun S2 rv =>
        init_object runs S2 C l pds') in
    match pb with
    | propbody_val e0 =>
      if_success_value runs C (runs_type_expr runs S C e0) (fun S1 v0 =>
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

Fixpoint run_var_decl runs S C xeos : result :=
  match xeos with
  | nil => out_ter S res_empty
  | (x, eo) :: xeos' =>
    if_success (match eo with
      | None => out_ter S undef
      | Some e =>
        if_success_value runs C (runs_type_expr runs S C e) (fun S1 v =>
          if_some (identifier_res S1 C x) (fun ir =>
            if_void (ref_put_value runs S1 C ir v) (fun S2 =>
              out_ter S2 undef)))
      end) (fun S1 rv =>
        run_var_decl runs S1 C xeos')
  end.

Fixpoint run_list_expr runs S1 C (vs : list value) (es : list expr)
  (K : state -> list value -> result) : result :=
  match es with
  | nil => K S1 (LibList.rev vs)
  | e :: es' =>
    if_success_value runs C (runs_type_expr runs S1 C e) (fun S2 v =>
      run_list_expr runs S2 C (v :: vs) es' K)
  end.

Fixpoint run_block runs S C rv ts : result :=
  match ts with
  | nil => out_ter S rv
  | t :: ts' =>
    if_success_state rv (runs_type_stat runs S C t) (fun S1 rv1 =>
      run_block runs S1 C rv1 ts')
  end.


(**************************************************************)
(** ** Intermediary functions for all non-trivial cases. *)

Definition run_expr_binary_op run_binary_op' runs S C op e1 e2 : result :=
  match is_lazy_op op with
  | None =>
    if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
      if_success_value runs C (runs_type_expr runs S1 C e2) (fun S2 v2 =>
        run_binary_op' S2 C op v1 v2))
  | Some b_ret =>
    if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
      let b1 := convert_value_to_boolean v1 in
      ifb b1 = b_ret then out_ter S1 v1
      else
        if_success_value runs C (runs_type_expr runs S1 C e2) out_ter)
  end.

Definition run_expr_access runs S C e1 e2 : result :=
  if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
    if_success_value runs C (runs_type_expr runs S C e2) (fun S2 v2 =>
      ifb v1 = prim_undef \/ v1 = prim_null then
        run_error S2 prealloc_ref_error
      else
        if_string (to_string runs S2 C v2) (fun S3 x =>
          out_ter S3 (ref_create_value v1 x (execution_ctx_strict C))))).

Definition run_expr_assign run_binary_op' runs S C (opo : option binary_op) e1 e2 : result :=
  if_success (runs_type_expr runs S C e1) (fun S1 rv1 =>
    let follow S rv' :=
      match rv' with
      | resvalue_value v =>
        if_void (ref_put_value runs S C rv1 v) (fun S' =>
         out_ter S' v)
      | _ => result_stuck
      end in
    match opo with
    | None =>
      if_success_value runs C (runs_type_expr runs S1 C e2) follow
    | Some op =>
      if_success_value runs C (out_ter S1 rv1) (fun S2 v1 =>
        if_success_value runs C (runs_type_expr runs S2 C e2) (fun S3 v2 =>
          if_success (run_binary_op' S3 C op v1 v2) follow))
    end).

Definition run_expr_function runs S C fo args bd : result :=
  match fo with
  | None =>
    let lex := execution_ctx_lexical_env C in
    creating_function_object runs S C args bd lex (funcbody_is_strict bd)
  | Some fn =>
    let (lex', S') := lexical_env_alloc_decl S (execution_ctx_lexical_env C) in
    let follow L :=
      let E := pick (env_record_binds S' L) in
      if_void (env_record_create_immutable_binding S' L fn) (fun S1 =>
        if_object (creating_function_object runs S1 C args bd lex' (funcbody_is_strict bd)) (fun S2 l =>
          if_void (env_record_initialize_immutable_binding S2 L fn l) (fun S3 =>
            out_ter S3 l))) in
    map_nth (fun _ : unit => result_stuck) (fun L _ => follow L) 0 lex' tt
  end.

Definition entering_eval_code runs S C direct bd K : result :=
  let C' := if direct then C else execution_ctx_initial false in
  let str := funcbody_is_strict bd in
  let (lex, S') :=
    if str
      then lexical_env_alloc_decl S (execution_ctx_lexical_env C')
      else (execution_ctx_lexical_env C', S)
    in
  let C1 :=
    if str
      then execution_ctx_with_lex_same C' lex
      else C'
    in
  let p := funcbody_prog bd in
  if_void (execution_ctx_binding_inst runs S' C1 codetype_eval None p nil) (fun S1 =>
    K S1 C').

Definition run_eval runs S C (is_direct_call : bool) (vthis : value) (vs : list value) : result := (* Corresponds to the rule [spec_call_global_eval] of the specification. *)
  match get_arg 0 vs with
  | prim_string s =>
    match pick (parse s) with
    | None =>
      run_error S prealloc_syntax_error
    | Some p =>
      entering_eval_code runs S C is_direct_call (funcbody_intro p s) (fun S1 C' =>
        if_ter (runs_type_prog runs S1 C' p) (fun S2 R =>
          match res_type R with
          | restype_throw =>
            out_ter S2 (res_throw (res_value R))
          | restype_normal =>
            match res_value R with
            | resvalue_value v =>
              out_ter S2 v
            | resvalue_empty =>
              out_ter S2 undef
            | resvalue_ref r =>
              result_stuck
            end
          | _ => result_stuck
          end))
    end
  | v => out_ter S v
  end.

Definition is_syntactic_eval e :=
  match e with
  | expr_literal (literal_string "eval") => true
  | _ => false
  end.

Definition run_expr_call runs S C e1 e2s : result :=
  let is_eval_direct := is_syntactic_eval e1 in
  if_success (runs_type_expr runs S C e1) (fun S1 rv =>
    if_success_value runs C (out_ter S1 rv) (fun S2 f =>
      run_list_expr runs S2 C nil e2s (fun S3 vs =>
        match f with
        | value_object l =>
          ifb ~ (is_callable S3 l) then run_error S3 prealloc_type_error
          else
            let follow vthis :=
              ifb l = prealloc_global_eval then
                run_eval runs S3 C is_eval_direct vthis vs
              else runs_type_call_full runs S3 C l vthis vs in
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
            | resvalue_empty => result_stuck
            end
        | value_prim _ => run_error S3 prealloc_type_error
        end))).

Definition run_expr_conditionnal runs S C e1 e2 e3 : result :=
  if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
    let b := convert_value_to_boolean v1 in
    let e := if b then e2 else e3 in
    if_success_value runs C (runs_type_expr runs S1 C e) out_ter).

Definition run_expr_new runs S C e1 (e2s : list expr) : result :=
  if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v =>
    run_list_expr runs S1 C nil e2s (fun S2 args =>
      match v with
      | value_object l =>
        match run_object_method object_construct_ S l with
        | None => run_error S2 prealloc_type_error
        | Some _ => run_construct runs S2 C l args
        end
      | value_prim _ =>
        run_error S2 prealloc_type_error
      end)).


(**************************************************************)

Definition run_stat_label runs S C lab t : result :=
  if_break (runs_type_stat runs S C t) (fun S1 R1 =>
    out_ter S1 (res_value R1)).

Definition run_stat_with runs S C e1 t2 : result :=
  if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
    if_object (to_object S1 v1) (fun S2 l =>
      let lex := execution_ctx_lexical_env C in
      let (lex', S3) := lexical_env_alloc_object S2 lex l provide_this_true in
      let C' := execution_ctx_with_lex_this C lex' l in
      runs_type_stat runs S3 C' t2)).

Definition run_stat_if runs S C e1 t2 to : result :=
  if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
    if (convert_value_to_boolean v1) then
      runs_type_stat runs S1 C t2
    else
      match to with
      | Some t3 =>
        runs_type_stat runs S1 C t3
      | None =>
        out_ter S resvalue_empty
      end).

Fixpoint run_stat_while (max_step : nat) runs rv S C ls e1 t2 : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_stat_while' := run_stat_while max_step' runs in
    if_success_value runs C (runs_type_expr runs S C e1) (fun S1 v1 =>
      if convert_value_to_boolean v1 then
        if_ter (runs_type_stat runs S1 C t2) (fun S2 R2 =>
          let rvR := res_value R2 in
          let rv' := ifb rvR = resvalue_empty then rv else rvR in
          if_normal_continue_or_break (out_ter S2 R2)
            (fun R => res_label_in R ls) (fun S3 R3 =>
            run_stat_while' rv' S3 C ls e1 t2) (fun S3 R3 =>
            out_ter S3 rv'))
      else out_ter S1 rv)
  end.

Definition run_stat_try runs S C t1 t2o t3o : result :=
  let finally res :=
    match t3o with
    | None => res
    | Some t3 =>
      if_ter res (fun S1 R =>
        if_success (runs_type_stat runs S1 C t3) (fun S2 rv' =>
          out_ter S2 R))
    end
  in
  if_any_or_throw (runs_type_stat runs S C t1) finally (fun S1 v =>
    match t2o with
    | None => finally (out_ter S1 (res_throw v))
    | Some (x, t2) =>
      let lex := execution_ctx_lexical_env C in
      let (lex', S') := lexical_env_alloc_decl S lex in
      match lex' with
      | L :: oldlex =>
        if_void (env_record_create_set_mutable_binding
          runs S C L x None v throw_irrelevant) (fun S2 =>
            let C' := execution_ctx_with_lex C lex' in
            finally (runs_type_stat runs S2 C' t2))
      | nil => result_stuck
      end
    end).

Definition run_stat_throw runs S C e : result :=
  if_success_value runs C (runs_type_expr runs S C e) (fun S1 v1 =>
    out_ter S (res_throw v1)).

Definition run_stat_return runs S C eo : result :=
  match eo with
  | None =>
    out_ter S (res_return undef)
  | Some e =>
    if_success_value runs C (runs_type_expr runs S C e) (fun S1 v1 =>
      out_ter S (res_return v1))
  end.


(**************************************************************)
(** ** Definition of the interpreter *)

Fixpoint run_expr (max_step : nat) S C e : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    let run_call_full' := run_call_full max_step' in
    let runs' := runs_type_intro run_expr' run_stat' run_prog' run_call' run_call_full' in
    let run_binary_op' := run_binary_op max_step' runs' in
    match e with

    | expr_literal i =>
      out_ter S (convert_literal_to_prim i)

    | expr_identifier x =>
      if_some (identifier_res S C x) (out_ter S)

    | expr_unary_op op e =>
      run_unary_op runs' S C op e

    | expr_binary_op e1 op e2 =>
      run_expr_binary_op run_binary_op' runs' S C op e1 e2

    | expr_object pds =>
      if_object (run_construct_prealloc runs' prealloc_object S C nil) (fun S1 l =>
        init_object runs' S1 C l pds)

    | expr_member e1 f =>
      runs_type_expr runs' S C (expr_access e1 (expr_literal (literal_string f)))

    | expr_access e1 e2 =>
      run_expr_access runs' S C e1 e2

    | expr_assign e1 opo e2 =>
      run_expr_assign run_binary_op' runs' S C opo e1 e2

    | expr_function fo args bd =>
      run_expr_function runs' S C fo args bd

    | expr_call e1 e2s =>
      run_expr_call runs' S C e1 e2s

    | expr_this =>
      out_ter S (execution_ctx_this_binding C)

    | expr_new e1 e2s =>
      run_expr_new runs' S C e1 e2s

    | expr_conditional e1 e2 e3 =>
      run_expr_conditionnal runs' S C e1 e2 e3

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
    let run_call_full' := run_call_full max_step' in
    let runs' := runs_type_intro run_expr' run_stat' run_prog' run_call' run_call_full' in
    match t with

    | stat_expr e =>
      if_success_value runs' C (run_expr' S C e) out_ter

    | stat_var_decl xeos =>
      run_var_decl runs' S C xeos

    | stat_block ts =>
      run_block runs' S C resvalue_empty ts

    | stat_label lab t =>
      run_stat_label runs' S C lab t

    | stat_with e1 t2 =>
      run_stat_with runs' S C e1 t2

    | stat_if e1 t2 to =>
      run_stat_if runs' S C e1 t2 to

    | stat_do_while ls t1 e2 =>
      arbitrary (* TODO *)

    | stat_while ls e1 t2 =>
      run_stat_while max_step' runs' resvalue_empty S C ls e1 t2

    | stat_throw e =>
      run_stat_throw runs' S C e

    | stat_try t1 t2o t3o =>
      run_stat_try runs' S C t1 t2o t3o

    | stat_return eo =>
      run_stat_return runs' S C eo

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

(**************************************************************)

with run_elements (max_step : nat) S C rv (els : list element) : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_stat' := run_stat max_step' in
    let run_elements' := run_elements max_step' in
    match els with

    | nil => out_ter S rv

    | element_stat t :: els' =>
      if_not_throw (run_stat' S C t) (fun S1 R1 =>
        let R2 := res_overwrite_value_if_empty rv R1 in
        if_success (out_ter S1 R2) (fun S2 rv2 => (* TODO:  wait for the specificatation to be updated. *)
          run_elements' S2 C rv2 els'))

    | element_func_decl name args bd :: els' =>
      run_elements' S C rv els'

    end
  end

(**************************************************************)

with run_prog (max_step : nat) S C p : result :=
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_elements' := run_elements max_step' in
    match p with

    | prog_intro str els =>
      run_elements' S C resvalue_empty els

    end
  end

(**************************************************************)

with run_call (max_step : nat) S C B (args : list value) : result := (* Corresponds to the [spec_call_prealloc] of the specification. *)
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    let run_call_full' := run_call_full max_step' in
    let runs' := runs_type_intro run_expr' run_stat' run_prog' run_call' run_call_full' in
    match B with

    | prealloc_global_is_nan =>
      let v := get_arg 0 args in
      if_number (to_number runs' S C v) (fun S0 n =>
        out_ter S0 (neg (decide (n = JsNumber.nan))))

    | prealloc_global_is_finite =>
      let v := get_arg 0 args in
      if_number (to_number runs' S C v) (fun S0 n =>
        out_ter S0 (neg (decide (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity))))

    | prealloc_object_get_proto_of =>
      let v := get_arg 0 args in
      ifb type_of v <> type_object then
        result_stuck
      else
        out_ter S (resvalue_ref (ref_create_value v "prototype" false))

    | prealloc_object_get_own_prop_descriptor =>
      arbitrary (* TODO:  Waiting for specification *)

    | prealloc_object_seal =>
      match get_arg 0 args with
      | value_object l =>
        let xs := pick (object_properties_keys_as_list S l)
        in (fix object_seal S0 xs : result :=
          match xs with
          | nil =>
            let S1 := run_object_heap_set_extensible false S0 l in
            out_ter S1 l
          | x :: xs' =>
            if_some (run_object_get_own_prop S0 l x) (fun D =>
              match D with
              | full_descriptor_some A =>
                let A' :=
                  if attributes_configurable A then
                    let Desc :=
                      descriptor_intro None None None None None (Some false)
                    in attributes_update A Desc
                  else A
                in if_void (object_define_own_prop S0 l x A' true) (fun S1 =>
                  object_seal S1 xs')
              | full_descriptor_undef => result_stuck
              end)
          end) S xs
      | value_prim _ => run_error S prealloc_type_error
      end

    | prealloc_object_is_sealed =>
      let v := get_arg 0 args in
      match v with
      | value_object l =>
        let xs := pick (object_properties_keys_as_list S l)
        in (fix object_is_sealed xs : result :=
          match xs with
          | nil =>
            out_ter S (neg (run_object_method object_extensible_ S l))
          | x :: xs' =>
            if_some (run_object_get_own_prop S l x) (fun D =>
              match D with
              | full_descriptor_some A =>
                if attributes_configurable A then
                  out_ter S false
                else object_is_sealed xs'
              | full_descriptor_undef => result_stuck
              end)
          end) xs
      | value_prim _ => run_error S prealloc_type_error
      end

    | prealloc_object_freeze =>
      let v := get_arg 0 args in
      match v with
      | value_object l =>
        let xs := pick (object_properties_keys_as_list S l)
        in (fix object_freeze S0 xs : result :=
          match xs with
          | nil =>
            let S1 := run_object_heap_set_extensible false S0 l
            in out_ter S1 l
          | x :: xs' =>
            if_some (run_object_get_own_prop S l x) (fun D =>
              match D with
              | full_descriptor_some A =>
                let A' :=
                  ifb attributes_is_data A /\ attributes_writable A then
                    let Desc :=
                      descriptor_intro None (Some false) None None None None
                    in attributes_update A Desc
                  else A
                in let A'' :=
                  if attributes_configurable A' then
                    let Desc :=
                      descriptor_intro None None None None None (Some false)
                    in attributes_update A' Desc
                  else A'
                in if_void (object_define_own_prop S0 l x A'' true) (fun S1 =>
                  object_freeze S1 xs')
              | full_descriptor_undef => result_stuck
              end)
          end) S xs
      | value_prim _ => run_error S prealloc_type_error
      end


    | prealloc_object_is_frozen =>
      let v := get_arg 0 args in
      match v with
      | value_object l =>
        let xs := pick (object_properties_keys_as_list S l)
        in (fix object_is_frozen xs : result :=
          match xs with
          | nil =>
            out_ter S (neg (run_object_method object_extensible_ S l))
          | x :: xs' =>
            if_some (run_object_get_own_prop S l x) (fun D =>
              let check_configurable A :=
                if attributes_configurable A then
                  out_ter S false : result
                else object_is_frozen xs'
              in match D with
              | attributes_data_of Ad =>
                if attributes_writable Ad then
                  out_ter S false
                else check_configurable Ad
              | attributes_accessor_of Aa =>
                check_configurable Aa
              | full_descriptor_undef => result_stuck
              end)
          end) xs
      | value_prim _ => run_error S prealloc_type_error
      end

    | prealloc_object_is_extensible =>
      let v := get_arg 0 args in
      match v with
      | value_object l =>
        out_ter S (run_object_method object_extensible_ S l)
      | value_prim _ => run_error S prealloc_type_error
      end

    | prealloc_object_prevent_extensions =>
      let v := get_arg 0 args in
      match v with
      | value_object l =>
        let O := pick (object_binds S l) in
        let O1 := object_with_extension O false in
        let S' := object_write S l O1 in
        out_ter S' l
      | value_prim _ => run_error S prealloc_type_error
      end

    | prealloc_object_proto_to_string =>
      let v := execution_ctx_this_binding C in
      match v with
      | undef => out_ter S "[object Undefined]"
      | null => out_ter S "[object Null]"
      | _ =>
        if_object (to_object S v) (fun S1 l =>
          let s := run_object_method object_class_ S l in
          out_ter S1 ("[object " ++ s ++ "]"))
      end

    | prealloc_object_proto_value_of =>
      to_object S (execution_ctx_this_binding C)

    | prealloc_object_proto_is_prototype_of =>
      let v := get_arg 0 args in
      match v with
      | value_prim w => out_ter S false
      | value_object l =>
        let vt := execution_ctx_this_binding C in
        if_object (to_object S vt) (fun S1 lo =>
          run_object_proto_is_prototype_of S1 lo l)
      end

    | prealloc_object_proto_prop_is_enumerable =>
      let v := get_arg 0 args in
      if_string (to_string runs' S C v) (fun S1 x =>
        if_object (to_object S1 (execution_ctx_this_binding C)) (fun S2 l =>
          if_some (run_object_get_own_prop S2 l x) (fun D =>
            match D with
            | full_descriptor_undef =>
              out_ter S2 false
            | full_descriptor_some A =>
              out_ter S2 (attributes_enumerable A)
            end)))

    | prealloc_function_proto =>
      out_ter S undef

    | prealloc_bool =>
      let v := get_arg 0 args in
      let b := convert_value_to_boolean v in
      let O1 := object_new prealloc_bool_proto "Boolean" in
      let O := object_with_primitive_value O1 b in
      let (l, S') := object_alloc S O in
      out_ter S' l

    | prealloc_bool_proto_to_string =>
      if_bool (bool_proto_value_of_call S C) (fun S b =>
        out_ter S (convert_bool_to_string b))

    | prealloc_bool_proto_value_of =>
      bool_proto_value_of_call S C

    | prealloc_number =>
      ifb args = nil then
        out_ter S JsNumber.zero
      else
        let v := get_arg 0 args in
        to_number runs' S C v

    | prealloc_number_proto_value_of =>
      let v := execution_ctx_this_binding C in
      match run_value_viewable_as_prim "Number" S v with
      | Some (prim_number n) => out_ter S n
      | _ => run_error S prealloc_type_error
      end

    | _ =>
      arbitrary (* TODO *)

    end
  end

with run_call_full (max_step : nat) S C l vthis args : result := (* Corresponds to the [spec_call] of the specification. *)
  match max_step with
  | O => result_bottom
  | S max_step' =>
    let run_expr' := run_expr max_step' in
    let run_stat' := run_stat max_step' in
    let run_prog' := run_prog max_step' in
    let run_call' := run_call max_step' in
    let run_call_full' := run_call_full max_step' in
    let runs' := runs_type_intro run_expr' run_stat' run_prog' run_call' run_call_full' in
    if_some (run_object_method object_call_ S l) (fun c =>
      match c with
      | call_default =>
        entering_func_code runs' S C l vthis args
      | call_prealloc B =>
        run_call' S C B args
      | call_after_bind => result_stuck
      end)
  end.

(**************************************************************)

Definition runs max_step :=
  let run_expr' := run_expr max_step in
  let run_stat' := run_stat max_step in
  let run_prog' := run_prog max_step in
  let run_call' := run_call max_step in
  let run_call_full' := run_call_full max_step in
  runs_type_intro run_expr' run_stat' run_prog' run_call' run_call_full'.

Definition run_javascript (max_step : nat) p : result :=
  let runs' := runs max_step in
  let S := state_initial in
  let p' := add_infos_prog strictness_false p in
  let C := execution_ctx_initial (prog_intro_strictness p) in
  if_void (execution_ctx_binding_inst runs' S C codetype_global None p nil) (fun S' =>
    runs_type_prog runs' S' C p').

End Interpreter.

