Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsSyntaxInfos JsPreliminary JsPreliminaryAux JsInit.
Require Import LibFix LibList.


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

Implicit Type T : Type.


(**************************************************************)
(** ** Structure of This File *)

(* Definitions of the datatypes used.
 * Monadic constructors.
 * Functions corresponding to the [spec_*] of the semantics.
 * Operatorshandling.
 * Functions corresponding to syntax cases of the semantics (while, if, ...)
 * Final fixed point. *)


(**************************************************************)
(** ** Some types used by the interpreter *)

(*
  * [result_some] is the normal result when the computation terminates normally.
  * [result_not_yet_implemented] means that this result is not implemented yet.
  * [result_impossible] should not happen and is probably the result of a broken invariant.
  * [result_bottom] means that the computation taked too long and we run out of fuel.
*)

Inductive resultof T :=
  | result_some : T -> resultof T
  | result_not_yet_implemented
  | result_impossible
  | result_bottom : state -> resultof T.

  (* We could put any information there.  They can be used to create step by step interpreter. *)

Implicit Arguments result_some [[T]].
Implicit Arguments result_not_yet_implemented [[T]].
Implicit Arguments result_impossible [[T]].
Implicit Arguments result_bottom [[T]].

(* It can be useful to get details on why a stuck is obtained. *)
(* The cases where [result_impossible] is directly used are the cases
  where it has been proven impossible to get it under normal condition.
  See [JsCorrectness.v] for more details. *)

Definition impossible_because {T} s : resultof T := result_impossible.

Definition impossible_with_heap_because {T} S s : resultof T := result_impossible.

(* Some special reduction rules does not return a usual triple (called [out] here), but a
  special value.  The following type is there to encapsulate that. *)

Definition specres T := resultof (specret T).

Definition res_out T o : specres T :=
  result_some (specret_out o).
Implicit Arguments res_out [[T]].

Definition res_spec T S a : specres T :=
  result_some (specret_val S a).

(* [result] is the most common result type, returning an [out] each time. *)
(* Note that this [out] does not necessarily (and hopefully rarely) aborts. *)
Inductive nothing : Type :=.
Definition retn := specret nothing.
Definition result := resultof retn.
Definition res_ter S R : result := res_out (out_ter S R).

Implicit Type W : result.

(* In the semantics, some rules returns an [out] which actually never
  carries a result, only an [out_void] of something (or an error).  The
  following type is there to differentiate those functions from the
  others. *)
(* It shall be replaced by a [specres unit]. *)
Definition result_void := result.

Definition res_void S : result_void := res_out (out_void S).

(* Coercion *)

Coercion result_some_out o : resultof out := result_some o.

Definition out_from_retn (sp : retn) : out :=
  match sp with
  | specret_val _ n => nothing_rect _ n
  | specret_out o => o
  end.

Coercion out_retn o : retn := specret_out o.
Coercion result_out o : result := res_out o.

Coercion res_to_res_void (W : result) : result_void := W.

(* Inhabited *)

Global Instance result_inhab : forall T, Inhab (resultof T).
Proof. introv. applys prove_Inhab @impossible_because. exact "Resultof is inhabited". Qed.


(**************************************************************)
(** ** Helper functions for the interpreter *)

Section InterpreterEliminations.

(**************************************************************)
(** Generic constructions *)

Definition get_arg := nth_def undef.

Definition destr_list (A B : Type) (l : list A) (d : B) f :=
  match l with
  | nil => d
  | cons a _ => f a
  end.


(**************************************************************)
(** Monadic Constructors *)

Definition if_empty_label T S R (K : unit -> resultof T) : resultof T :=
  ifb res_label R = label_empty then K tt
  else
    impossible_with_heap_because S "[if_empty_label] received a normal result with non-empty label.".

Definition if_some (A B : Type) (op : option A) (K : A -> resultof B) : resultof B :=
  match op with
  | None => impossible_because "[if_some] called with [None]."
  | Some a => K a
  end.

Definition if_some_or_default (A B : Type) (o : option B) (d : A) (K : B -> A) : A :=
  option_case d K o.

Definition if_result_some (A B : Type) (W : resultof A) (K : A -> resultof B) : resultof B :=
  match W with
  | result_some a => K a
  | result_not_yet_implemented => result_not_yet_implemented
  | result_impossible => result_impossible
  | result_bottom S0 => result_bottom S0
  end.

Definition if_out_some T W (K : out -> resultof T) : resultof T :=
  if_result_some W (fun sp => K (out_from_retn sp)).

Definition throw_result T W : specres T := (* Returns a [res_out], formatted into a [specres T]. *)
  if_out_some W (fun o => res_out o).

Definition if_ter T W (K : state -> res -> specres T) : specres T :=
  if_out_some W (fun o =>
    match o with
    | out_ter S0 R => K S0 R
    | _ => res_out o
    end).

Definition if_success_state rv W (K : state -> resvalue -> result) : result :=
  if_ter W (fun S0 R =>
    match res_type R with
    | restype_normal =>
      if_empty_label S0 R (fun _ =>
        K S0 (ifb res_value R = resvalue_empty then rv else res_value R))
    | restype_throw => res_ter S0 R
    | _ =>
      res_ter S0 (res_overwrite_value_if_empty rv R)
    end).

Definition if_success T W (K : state -> resvalue -> specres T) : specres T :=
  if_ter W (fun S0 R =>
    match res_type R with
    | restype_normal =>
      if_empty_label S0 R (fun _ =>
        K S0 (res_value R))
    | _ =>
      res_out (out_ter S0 R)
    end).

Definition if_void (W : result_void) (K : state -> result) : result :=
  if_success W (fun S rv =>
    match rv with
    | resvalue_empty => K S
    | _ =>
      impossible_with_heap_because S "[if_void called] with non-void result value."
    end).

Definition if_not_throw W (K : state -> res -> result) : result :=
  if_ter W (fun S0 R =>
    match res_type R with
    | restype_throw => W
    | _ => K S0 R
    end).

Definition if_any_or_throw W (K1 : state -> res -> result)
    (K2 : state -> value -> result) : result :=
  if_ter W (fun S R =>
    match res_type R with
    | restype_throw =>
      match res_value R with
      | resvalue_value v =>
        if_empty_label S R (fun _ =>
          K2 S v)
      | _ =>
        impossible_with_heap_because S "[if_any_or_throw] called with a non-value result."
      end
    | _ => K1 S R
    end).

Definition if_success_or_return W (K1 : state -> result) (K2 : state -> resvalue -> result) : result :=
  if_ter W (fun S R =>
    match res_type R with
    | restype_normal =>
      if_empty_label S R (fun _ => K1 S)
    | restype_return =>
      if_empty_label S R (fun _ => K2 S (res_value R))
    | _ => W
    end).

Definition if_break W (K : state -> res -> result) : result :=
  if_ter W (fun S R =>
    match res_type R with
    | restype_break => K S R
    | _ => res_ter S R
    end).

Definition if_value T W (K : state -> value -> specres T) : specres T :=
  if_success W (fun S rv =>
    match rv with
    | resvalue_value v => K S v
    | _ =>
      impossible_with_heap_because S "[if_value] called with non-value."
    end).

Definition if_bool T W (K : state -> bool -> specres T) : specres T :=
  if_value W (fun S v =>
    match v with
    | prim_bool b => K S b
    | _ =>
      impossible_with_heap_because S "[if_bool] called with non-boolean value."
    end).

Definition if_object T W (K : state -> object_loc -> specres T) : specres T :=
  if_value W (fun S v =>
    match v with
    | value_object l => K S l
    | value_prim _ =>
      impossible_with_heap_because S "[if_object] called on a primitive."
    end).

Definition if_string T W (K : state -> string -> specres T) : specres T :=
  if_value W (fun S v =>
    match v with
    | prim_string s => K S s
    | _ =>
      impossible_with_heap_because S "[if_string] called on a non-string value."
    end).

Definition if_number T W (K : state -> number -> specres T) : specres T :=
  if_value W (fun S v =>
    match v with
    | prim_number n => K S n
    | _ =>
      impossible_with_heap_because S "[if_number] called with non-number value."
    end).

Definition if_prim T W (K : state -> prim -> specres T) : specres T :=
  if_value W (fun S v =>
    match v with
    | value_prim w => K S w
    | value_object _ =>
      impossible_with_heap_because S "[if_primitive] called on an object."
    end).

Definition convert_option_attributes : option attributes -> option full_descriptor :=
  LibOption.map (fun A => A : full_descriptor).

Definition if_abort (T:Type) o (K : unit -> resultof T) : resultof T :=
  match o with
  | out_ter S0 R =>
    ifb res_type R = restype_normal then
      impossible_with_heap_because S0 "[if_abort] received a normal result!"
    else K tt
  | _ => K tt
  end.

Definition if_spec (A B : Type) (W : specres A) (K : state -> A -> specres B) : specres B :=
  if_result_some W (fun sp =>
    match sp with
    | specret_val S0 a => K S0 a
    | specret_out o =>
      if_abort o (fun _ =>
        res_out o)
    end).

End InterpreterEliminations.
Implicit Arguments throw_result [[T]].

Section LexicalEnvironments.


(**************************************************************)
(** Error Handling *)

Definition build_error S vproto vmsg : result :=
  let O := object_new vproto "Error" in
  let '(l, S') := object_alloc S O in
  ifb vmsg = undef then out_ter S' l
  else result_not_yet_implemented (* LATER:  Need [to_string] (this function shall be put in [runs_type].) *).

Definition run_error T S ne : specres T :=
  if_object (build_error S (prealloc_native_error_proto ne) undef) (fun S' l =>
    result_some (specret_out (out_ter S' (res_throw l)))).
Implicit Arguments run_error [[T]].

(** [out_error_or_void S str ne R] throws the error [ne] if
    [str] is true, empty otherwise. *)

Definition out_error_or_void S str ne : result :=
  if str then run_error S ne
  else out_void S.

(** [out_error_or_cst S str ne v] throws the error [ne] if
    [str] is true, the value [v] otherwise. *)

Definition out_error_or_cst S str ne v : result :=
  if str then run_error S ne
  else out_ter S v.


(**************************************************************)
(** Operations on objects *)

Definition run_object_method Z (Proj : object -> Z) S l : option Z :=
  LibOption.map Proj (pick_option (object_binds S l)).

Definition run_object_heap_set_extensible b S l : option state :=
  LibOption.map (fun O =>
    object_write S l (object_set_extensible O b))
    (pick_option (object_binds S l)).


(**************************************************************)
(* The functions taking such arguments can call any arbitrary code,
   i.e. can also call arbitrary pogram and expression.  They thus need
   a pointer to the main functions.  Those types are just the ones of
   those main functions. *)

(* TODO: runs_type_to_integer, runs_type_to_string: There may be one, but I see no immediate reason for those two functions to be put inside [runs_type]. *)

Record runs_type : Type := runs_type_intro {
    runs_type_expr : state -> execution_ctx -> expr -> result;
    runs_type_stat : state -> execution_ctx -> stat -> result;
    runs_type_prog : state -> execution_ctx -> prog -> result;
    runs_type_call : state -> execution_ctx -> object_loc -> value -> list value -> result;
    runs_type_function_has_instance : state -> object_loc -> value -> result;
    runs_type_stat_while : state -> execution_ctx -> resvalue -> label_set -> expr -> stat -> result;
    runs_type_stat_do_while : state -> execution_ctx -> resvalue -> label_set -> expr -> stat -> result;
    runs_type_stat_for_loop : state -> execution_ctx -> label_set -> resvalue -> option expr -> option expr -> stat -> result;
    runs_type_object_delete : state -> execution_ctx -> object_loc -> prop_name -> bool -> result;
    runs_type_object_get_own_prop : state -> execution_ctx -> object_loc -> prop_name -> specres full_descriptor;
    runs_type_object_get_prop : state -> execution_ctx -> object_loc -> prop_name -> specres full_descriptor;
    runs_type_object_get : state -> execution_ctx -> object_loc -> prop_name -> result;
    runs_type_object_proto_is_prototype_of : state -> object_loc -> object_loc -> result;
    runs_type_object_put : state -> execution_ctx -> object_loc -> prop_name -> value -> strictness_flag -> result;
    runs_type_equal : state -> execution_ctx -> value -> value -> result;
    runs_type_to_integer : state -> execution_ctx -> value -> result;
    runs_type_to_string : state -> execution_ctx -> value -> result
  }.

Implicit Type runs : runs_type.


(**************************************************************)
(** Object Get *)

Definition object_has_prop runs S C l x : result :=
  if_some (run_object_method object_has_prop_ S l) (fun B =>
    match B with
    | builtin_has_prop_default =>
      if_spec (runs_type_object_get_prop runs S C l x) (fun S1 D =>
        res_ter S1 (decide (D <> full_descriptor_undef)))
    end).

Definition object_get_builtin runs S C B (vthis : value) l x : result :=
  (* Corresponds to the construction [spec_object_get_1] of the specification. *)

  'let default :=
    fun S l =>
      if_spec (runs_type_object_get_prop runs S C l x) (fun S0 D =>
        match D with
        | full_descriptor_undef =>
          res_ter S0 undef
        | attributes_data_of Ad =>
          res_ter S0 (attributes_data_value Ad)
        | attributes_accessor_of Aa =>
            match attributes_accessor_get Aa with
            | value_object lf =>
              runs_type_call runs S0 C lf vthis nil
            | undef =>
              res_ter S0 undef
            | value_prim _ =>
              result_impossible (* At least, the ECMAScript specification says so. *)
            end
        end) in

  'let function :=
    fun S =>
      if_value (default S l) (fun S' v =>
         ifb spec_function_get_error_case S' x v then
           run_error S' native_error_type
         else
           res_ter S' v
      ) in

  match B with
  | builtin_get_default => default S l

  | builtin_get_function => function S

  | builtin_get_args_obj =>
    if_some (run_object_method object_parameter_map_ S l) (fun lmapo =>
      if_some lmapo (fun lmap =>
        if_spec (runs_type_object_get_own_prop runs S C lmap x) (fun S D =>
          match D with
          | full_descriptor_undef => function S
          | _ => runs_type_object_get runs S C lmap x
          end)))
  end.

Definition run_object_get runs S C l x : result :=
  if_some (run_object_method object_get_ S l) (fun B =>
    object_get_builtin runs S C B l l x).

Definition run_object_get_prop runs S C l x : specres full_descriptor :=
  if_some (run_object_method object_get_prop_ S l) (fun B =>
    match B with
    | builtin_get_prop_default =>
      if_spec (runs_type_object_get_own_prop runs S C l x) (fun S1 D =>
        ifb D = full_descriptor_undef then (
          if_some (run_object_method object_proto_ S1 l) (fun proto =>
            match proto with
            | value_object lproto =>
              runs_type_object_get_prop runs S1 C lproto x
            | null =>
              res_spec S1 full_descriptor_undef
            | value_prim _ =>
              impossible_with_heap_because S1 "Found a non-null primitive value as a prototype in [run_object_get_prop]."
            end)
        ) else res_spec S1 D)
    end).


(* LATER Object.prototype.isPrototypeOf(V) should take a value, not a location. Spec is fine. *)
Definition object_proto_is_prototype_of runs S l0 l : result :=
  if_some (run_object_method object_proto_ S l) (fun B =>
    match B return result with
    | null => out_ter S false
    | value_object l' =>
      ifb l' = l0
        then out_ter S true
        else runs_type_object_proto_is_prototype_of runs S l0 l'
    | value_prim _ =>
      impossible_with_heap_because S "[run_object_method] returned a primitive in [object_proto_is_prototype_of_body]."
    end).


(**************************************************************)
(** Object Set *)

Definition object_can_put runs S C l x : result :=
  if_some (run_object_method object_can_put_ S l) (fun B =>
      match B with
      | builtin_can_put_default =>
        if_spec (runs_type_object_get_own_prop runs S C l x) (fun S1 D =>
          match D with
          | attributes_accessor_of Aa =>
            res_ter S1 (decide (attributes_accessor_set Aa <> undef))
          | attributes_data_of Ad =>
            res_ter S1 (attributes_data_writable Ad)
          | full_descriptor_undef =>
            if_some (run_object_method object_proto_ S1 l) (fun vproto =>
                match vproto with
                | null =>
                  if_some (run_object_method object_extensible_ S1 l)
                    (fun b => res_ter S1 b)
                | value_object lproto =>
                  if_spec (run_object_get_prop runs S1 C lproto x) (fun S2 D' =>
                    match D' with
                    | full_descriptor_undef =>
                      if_some (run_object_method object_extensible_ S2 l)
                        (fun b => res_ter S2 b)
                    | attributes_accessor_of Aa =>
                      res_ter S2 (decide (attributes_accessor_set Aa <> undef))
                    | attributes_data_of Ad =>
                      if_some (run_object_method object_extensible_ S2 l) (fun ext =>
                        res_ter S2 (
                          if ext then attributes_data_writable Ad
                          else false))
                  end)
                | value_prim _ =>
                  impossible_with_heap_because S1 "Non-null primitive get as a prototype value in [object_can_put]."
                end)
          end)
      end).


Definition object_define_own_prop runs S C l x Desc throw : result :=
  'let reject := fun S throw =>
    out_error_or_cst S throw native_error_type false in

  'let default := fun S throw =>
      if_spec (runs_type_object_get_own_prop runs S C l x) (fun S1 D =>
        if_some (run_object_method object_extensible_ S1 l) (fun ext =>
             match D, ext with
             | full_descriptor_undef, false => reject S1 throw
             | full_descriptor_undef, true =>
               'let A : attributes :=
                 ifb descriptor_is_generic Desc \/ descriptor_is_data Desc
                 then (attributes_data_of_descriptor Desc : attributes)
                 else attributes_accessor_of_descriptor Desc in
               if_some (pick_option (object_set_property S1 l x A)) (fun S2 =>
                 res_ter S2 true)
             | full_descriptor_some A, bext =>
               'let object_define_own_prop_write := fun S1 A =>
                 let A' := attributes_update A Desc in
                 if_some (pick_option (object_set_property S1 l x A')) (fun S2 =>
                   res_ter S2 true)
                 in
               ifb descriptor_contains A Desc then
                 res_ter S1 true
               else ifb attributes_change_enumerable_on_non_configurable A Desc then
                 reject S1 throw
               else ifb descriptor_is_generic Desc then
                 object_define_own_prop_write S1 A
               else ifb attributes_is_data A <> descriptor_is_data Desc then
                 (* LATER: restore version with negation:
                 if neg (attributes_configurable A) then
                   reject S1
                 else
                   let A':=
                     match A return attributes with
                     | attributes_data_of Ad =>
                       attributes_accessor_of_attributes_data Ad
                     | attributes_accessor_of Aa =>
                       attributes_data_of_attributes_accessor Aa
                     end in
                   if_some (pick_option (object_set_property S1 l x A')) (fun S2 =>
                        object_define_own_prop_write S2 A')
                  *)
                 (if (attributes_configurable A) then
                   'let A':=
                     match A return attributes with
                     | attributes_data_of Ad =>
                       attributes_accessor_of_attributes_data Ad
                     | attributes_accessor_of Aa =>
                       attributes_data_of_attributes_accessor Aa
                     end in
                   if_some (pick_option (object_set_property S1 l x A')) (fun S2 =>
                        object_define_own_prop_write S2 A')
                 else
                   reject S1 throw)
               else ifb (attributes_is_data A /\ descriptor_is_data Desc) then
                 match A with
                 | attributes_data_of Ad =>
                   ifb attributes_change_data_on_non_configurable Ad Desc then
                     reject S1 throw
                   else
                     object_define_own_prop_write S1 A
                 | attributes_accessor_of _ =>
                   impossible_with_heap_because S "data is not accessor in [defineOwnProperty]"
                 end
               else ifb (not (attributes_is_data A) /\ descriptor_is_accessor Desc) then
                 match A with
                 | attributes_accessor_of Aa =>
                   ifb attributes_change_accessor_on_non_configurable Aa Desc then
                     reject S1 throw
                   else
                     object_define_own_prop_write S1 A
                 | attributes_data_of _ =>
                   impossible_with_heap_because S "accessor is not data in [defineOwnProperty]"
                 end
               else
                (* LATER: check this is true *)
                impossible_with_heap_because S "cases are mutually exclusives in [defineOwnProperty]"
             end)) in

  if_some (run_object_method object_define_own_prop_ S l) (fun B =>
    match B with
    | builtin_define_own_prop_default => default S throw
    | builtin_define_own_prop_args_obj =>
      if_some (run_object_method object_parameter_map_ S l) (fun lmapo =>
        if_some lmapo (fun lmap =>
          if_spec (runs_type_object_get_own_prop runs S C lmap x) (fun S D =>
            if_bool (default S false) (fun S b =>
              if b then
                'let follow := fun S => res_ter S true in
                match D with
                | full_descriptor_undef =>
                  follow S
                | full_descriptor_some A =>
                  ifb descriptor_is_accessor Desc
                  then if_bool (runs_type_object_delete runs S C lmap x false) (fun S _ =>
                         follow S)
                  else 'let follow := fun S =>
                         ifb descriptor_writable Desc = Some false then
                           if_bool (runs_type_object_delete runs S C lmap x false) (fun S _ =>
                             follow S)
                         else follow S
                         in

                       match descriptor_value Desc with
                       | Some v =>
                         if_void (runs_type_object_put runs S C lmap x v throw) (fun S =>
                           follow S)
                       | _ =>
                         follow S
                       end
                end
              else reject S throw))))
    end).

Definition run_to_descriptor runs S C v : specres descriptor :=
  match v with
  | value_prim _ =>
    run_error S native_error_type
  | value_object l =>
    let sub S Desc name conv K :=
      if_bool (object_has_prop runs S C l name) (fun S1 has =>
        if neg has then
          K S1 Desc
        else
          if_value (run_object_get runs S1 C l name) (fun S2 v =>
            if_spec (conv S2 v Desc) K)) in
    sub S descriptor_intro_empty "enumerable" (fun S1 v1 Desc =>
      let b := convert_value_to_boolean v1 in
      res_spec S1 (descriptor_with_enumerable Desc (Some b))) (fun S1' Desc =>
        sub S1' Desc "configurable" (fun S2 v2 Desc =>
          let b := convert_value_to_boolean v2 in
          res_spec S2 (descriptor_with_configurable Desc (Some b))) (fun S2' Desc =>
            sub S2' Desc "value" (fun S3 v3 Desc =>
              res_spec S3 (descriptor_with_value Desc (Some v3))) (fun S3' Desc =>
                sub S3' Desc "writable" (fun S4 v4 Desc =>
                  let b := convert_value_to_boolean v4 in
                  res_spec S4 (descriptor_with_writable Desc (Some b))) (fun S4' Desc =>
                    sub S4' Desc "get" (fun S5 v5 Desc =>
                      ifb (is_callable S5 v5 = false) /\ v5 <> undef then
                        res_spec S5 (descriptor_with_get Desc (Some v5))
                      else run_error S5 native_error_type) (fun S5' Desc =>
                        sub S5' Desc "set" (fun S6 v6 Desc =>
                          ifb (is_callable S6 v6 = false) /\ v6 <> undef then
                            res_spec S6 (descriptor_with_set Desc (Some v6))
                          else run_error S6 native_error_type) (fun S7 Desc =>
                            ifb descriptor_inconsistent Desc then
                              run_error S7 native_error_type
                            else res_spec S7 Desc))))))

  end.


(**************************************************************)
(** Conversions *)

Definition prim_new_object S w : result :=
  match w with
  | prim_bool b =>
      'let O1 := object_new prealloc_bool_proto "Boolean" in
      'let O := object_with_primitive_value O1 b in
      let '(l, S1) := object_alloc S O in
      out_ter S1 l
  | prim_number n =>
      'let O1 := object_new prealloc_number_proto "Number" in
      'let O := object_with_primitive_value O1 n in
      let '(l, S1) := object_alloc S O in
      out_ter S1 l
  | prim_string s =>
      'let O2 := object_new prealloc_string_proto "String" in
      'let O1 := object_with_get_own_property O2 builtin_get_own_prop_string in
      'let O :=  object_with_primitive_value O1 s in
      let '(l, S1) := object_alloc S O in
      out_ter S1 l
  | _ =>
    impossible_with_heap_because S "[prim_new_object] received an null or undef."
  end.

Definition to_object S v : result :=
  match v with
  | prim_null => run_error S native_error_type
  | prim_undef => run_error S native_error_type
  | value_prim w => prim_new_object S w
  | value_object l => out_ter S l
  end.

Definition run_object_prim_value S l : result :=
  if_some (run_object_method object_prim_value_ S l) (fun (ov : option value) =>
    if_some ov (fun v =>
      res_ter S v)).

Definition prim_value_get runs S C v x : result :=
  if_object (to_object S v) (fun S' l =>
    object_get_builtin runs S' C builtin_get_default v l x).

Definition run_value_viewable_as_prim s S v : option (option prim) :=
  match v with
  | value_prim w => Some (Some w)
  | value_object l =>
      if_some_or_default (run_object_method object_class_ S l)
        None (fun s =>
          if_some_or_default (run_object_method object_prim_value_ S l)
            None (fun wo => Some (
              match wo with
              | Some (value_prim w) => Some w
              | _ => None
              end)))
  end.


(**************************************************************)
(** Operations on environments *)

Definition env_record_has_binding runs S C L x : result :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E return result with
    | env_record_decl Ed =>
      out_ter S (decide (decl_env_record_indom Ed x))
    | env_record_object l pt =>
      object_has_prop runs S C l x
    end).

Fixpoint lexical_env_get_identifier_ref runs S C X x str : specres ref :=
  match X with
  | nil =>
    res_spec S (ref_create_value undef x str)
  | L :: X' =>
    if_bool (env_record_has_binding runs S C L x) (fun S1 has =>
      if has then
        res_spec S1 (ref_create_env_loc L x str)
      else
        lexical_env_get_identifier_ref runs S1 C X' x str)
  end.

Definition object_delete_default runs S C l x str : result :=
  if_spec (runs_type_object_get_own_prop runs S C l x) (fun S1 D =>
    match D with
    | full_descriptor_undef => res_ter S1 true
    | full_descriptor_some A =>
      if attributes_configurable A then
        if_some (pick_option (object_rem_property S1 l x)) (fun S' =>
          res_ter S' true)
      else
        out_error_or_cst S1 str native_error_type false
    end).

Definition object_delete runs S C l x str : result :=
  if_some (run_object_method object_delete_ S l) (fun B =>
    match B with
    | builtin_delete_default =>
      object_delete_default runs S C l x str
    | builtin_delete_args_obj =>
      if_some (run_object_method object_parameter_map_ S l) (fun Mo =>
        if_some Mo (fun M =>
         if_spec (runs_type_object_get_own_prop runs S C M x) (fun S1 D =>
           if_bool (object_delete_default runs S1 C l x str) (fun S2 b =>
             match b, D with
             | true, full_descriptor_some _ =>
               if_bool (runs_type_object_delete runs S2 C M x false) (fun S3 b' =>
                 res_ter S3 b)
             | _, _ => res_ter S2 b
             end))))
    end).

Definition env_record_delete_binding runs S C L x : result :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      match Heap.read_option Ed x return result with
      | None =>
          out_ter S true
      | Some (mutability_deletable, v) =>
        let S' := env_record_write S L (decl_env_record_rem Ed x) in
        out_ter S' true
      | Some (mu, v) =>
        out_ter S false
      end
    | env_record_object l pt =>
      runs_type_object_delete runs S C l x throw_false
    end).

Definition env_record_implicit_this_value S L : option value :=
  if_some_or_default (pick_option (env_record_binds S L))
    None (fun E => Some (
      match E with
      | env_record_decl Ed => undef
      | env_record_object l provide_this =>
        if provide_this then l else undef
      end)).

Definition identifier_resolution runs S C x : specres ref :=
  let X := execution_ctx_lexical_env C in
  let str := execution_ctx_strict C in
  lexical_env_get_identifier_ref runs S C X x str.

Definition env_record_get_binding_value runs S C L x str : result :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      if_some (Heap.read_option Ed x) (fun rm =>
        let '(mu, v) := rm in
        ifb mu = mutability_uninitialized_immutable then
          out_error_or_cst S str native_error_ref undef
        else res_ter S v)
    | env_record_object l pt =>
      if_bool (object_has_prop runs S C l x) (fun S1 has =>
        if has then
          run_object_get runs S1 C l x
        else out_error_or_cst S1 str native_error_ref undef)
    end).


(**************************************************************)

Definition ref_get_value runs S C rv : specres value :=
  match rv with
  | resvalue_empty =>
    impossible_with_heap_because S "[ref_get_value] received an empty result."
  | resvalue_value v =>
    res_spec S v
  | resvalue_ref r =>
    'let for_base_or_object := fun tt =>
      match ref_base r with
      | ref_base_type_value v =>
        ifb ref_has_primitive_base r then
          if_value (prim_value_get runs S C v (ref_name r)) (@res_spec _)
        else
          match v with
           | value_object l =>
             if_value (run_object_get runs S C l (ref_name r)) (@res_spec _)
           | value_prim _ =>
             impossible_with_heap_because S "[ref_get_value] received a primitive value whose kind is not primitive."
          end
      | ref_base_type_env_loc L =>
        impossible_with_heap_because S "[ref_get_value] received a reference to a value whose base type is an environnment record."
      end
     in
    match ref_kind_of r with
    | ref_kind_null =>
      impossible_with_heap_because S "[ref_get_value] received a reference whose base is [null]."
    | ref_kind_undef =>
      throw_result (run_error S native_error_ref)
    | ref_kind_primitive_base | ref_kind_object =>
      for_base_or_object tt
    | ref_kind_env_record =>
      match ref_base r with
      | ref_base_type_value v =>
        impossible_with_heap_because S "[ref_get_value] received a reference to an environnment record whose base type is a value."
      | ref_base_type_env_loc L =>
        if_value (env_record_get_binding_value runs S C L (ref_name r) (ref_strict r))
          (@res_spec _)
      end
    end
  end.


Definition run_expr_get_value runs S C e : specres value :=
  if_success (runs_type_expr runs S C e) (fun S0 rv =>
    ref_get_value runs S0 C rv).

Definition object_put_complete runs B S C vthis l x v str : result_void :=
  match B with
  | builtin_put_default =>
    if_bool (object_can_put runs S C l x) (fun S1 b =>
      if b then
        if_spec (runs_type_object_get_own_prop runs S1 C l x) (fun S2 D =>
          'let follow := fun _ =>
            if_spec (run_object_get_prop runs S2 C l x) (fun S3 D' =>
              'let follow' := fun _ =>
                match vthis with
                | value_object lthis =>
                  'let Desc := descriptor_intro_data v true true true in
                  if_success (object_define_own_prop runs S3 C l x Desc str) (fun S4 rv =>
                    res_void S4)
                | value_prim wthis =>
                  out_error_or_void S3 str native_error_type
                end in
              match D' with
              | attributes_accessor_of Aa' =>
                match attributes_accessor_set Aa' with
                | value_object lfsetter =>
                  if_success (runs_type_call runs S3 C lfsetter vthis (v::nil)) (fun S4 rv =>
                    res_void S4)
                | value_prim _ =>
                  impossible_with_heap_because S3 "[object_put_complete] found a primitive in an `set' accessor."
                end
              | _ => follow' tt
              end) in
          match D with

          | attributes_data_of Ad =>
            match vthis with
            | value_object lthis =>
              'let Desc := descriptor_intro (Some v) None None None None None in
              if_success (object_define_own_prop runs S2 C l x Desc str) (fun S3 rv =>
                res_void S3)
            | value_prim wthis =>
              out_error_or_void S2 str native_error_type
            end

          | _ => follow tt

          end)
        else
          out_error_or_void S1 str native_error_type)
    end.

Definition object_put runs S C l x v str : result_void :=
  if_some (run_object_method object_put_ S l) (fun B =>
    object_put_complete runs B S C l l x v str).

Definition env_record_set_mutable_binding runs S C L x v str : result_void :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      if_some (Heap.read_option Ed x) (fun rm =>
        let '(mu, v_old) := rm in
        ifb mutability_is_mutable mu then
          res_void (env_record_write_decl_env S L x mu v)
        else out_error_or_void S str native_error_type)
    | env_record_object l pt =>
      object_put runs S C l x v str
    end).

Definition prim_value_put runs S C w x v str : result_void :=
  if_object (to_object S w) (fun S1 l =>
    object_put_complete runs builtin_put_default S1 C w l x v str).


Definition ref_put_value runs S C rv v : result_void :=
  match rv with
  | resvalue_value v => run_error S native_error_ref
  | resvalue_ref r =>
    ifb ref_is_unresolvable r then (
      if ref_strict r then
        run_error S native_error_ref
      else
        object_put runs S C prealloc_global (ref_name r) v throw_false)
    else ifb ref_is_property r then
      (* LATER: simplify impossible cases*)
      match ref_base r with
      | ref_base_type_value v' =>
        ifb ref_kind_of r = ref_kind_primitive_base then
          match v' with
          | value_prim w => prim_value_put runs S C w (ref_name r) v (ref_strict r)
          | _ => impossible_with_heap_because S "[ref_put_value] impossible case"
          end
        else
          match v' with
          | value_object l => object_put runs S C l (ref_name r) v (ref_strict r)
          | _ => impossible_with_heap_because S "[ref_put_value] impossible case"
          end
      | ref_base_type_env_loc L =>
        impossible_with_heap_because S "[ref_put_value] contradicts ref_is_property"
      end
    else
      match ref_base r with
      | ref_base_type_value _ =>
        impossible_with_heap_because S "[ref_put_value] impossible spec"
      | ref_base_type_env_loc L =>
        env_record_set_mutable_binding runs S C L (ref_name r) v (ref_strict r)
      end
  | resvalue_empty =>
    impossible_with_heap_because S "[ref_put_value] received an empty result."
  end.

Definition env_record_create_mutable_binding runs S C L x (deletable_opt : option bool) : result_void :=
  'let deletable := unsome_default false deletable_opt in
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      ifb decl_env_record_indom Ed x then
        impossible_with_heap_because S "Already declared environnment record in [env_record_create_mutable_binding]."
      else
        'let S' := env_record_write_decl_env S L x (mutability_of_bool deletable) undef in
        res_void S'
    | env_record_object l pt =>
      if_bool (object_has_prop runs S C l x) (fun S1 has =>
        if has then
          impossible_with_heap_because S1 "Already declared binding in [env_record_create_mutable_binding]."
        else (
          'let A := attributes_data_intro undef true true deletable in
          if_success (object_define_own_prop runs S1 C l x A throw_true) (fun S2 rv =>
            res_void S2)))
    end).

Definition env_record_create_set_mutable_binding runs S C L x (deletable_opt : option bool) v str : result_void :=
  if_void (env_record_create_mutable_binding runs S C L x deletable_opt) (fun S =>
    env_record_set_mutable_binding runs S C L x v str).

Definition env_record_create_immutable_binding S L x : result_void :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      ifb decl_env_record_indom Ed x then
        impossible_with_heap_because S "Already declared environnment record in [env_record_create_immutable_binding]."
      else
        res_void (env_record_write_decl_env S L x mutability_uninitialized_immutable undef)
    | env_record_object _ _ =>
        impossible_with_heap_because S "[env_record_create_immutable_binding] received an environnment record object."
    end).

Definition env_record_initialize_immutable_binding S L x v : result_void :=
  if_some (pick_option (env_record_binds S L)) (fun E =>
    match E with
    | env_record_decl Ed =>
      if_some (pick_option (Heap.binds Ed x)) (fun evs =>
        ifb evs = (mutability_uninitialized_immutable, undef) then
          'let S' := env_record_write_decl_env S L x mutability_immutable v in
          res_void S'
        else
          impossible_with_heap_because S "Non suitable binding in [env_record_initialize_immutable_binding].")
    | env_record_object _ _ => impossible_with_heap_because S "[env_record_initialize_immutable_binding] received an environnment record object."
    end).


(**************************************************************)
(** Conversions *)

Definition object_default_value runs S C l (prefo : option preftype) : result :=
  if_some (run_object_method object_default_value_ S l) (fun B =>
    match B with

    | builtin_default_value_default =>
      let gpref := unsome_default preftype_number prefo in
      let lpref := other_preftypes gpref in
      'let sub := fun S' x (K:state->result) =>
        (if_value (run_object_get runs S' C l x) (fun S1 vfo =>
          if_some (run_callable S1 vfo) (fun co =>
            match co with
            | Some B =>
              if_object (out_ter S1 vfo) (fun S2 lfunc =>
                if_value (runs_type_call runs S2 C lfunc l nil) (fun S3 v =>
                  match v return result with
                  | value_prim w => out_ter S3 w
                  | value_object l => K S3
                  end))
            | None => K S1
            end))) in
      'let gmeth := method_of_preftype gpref in
      sub S gmeth (fun S' =>
        let lmeth := method_of_preftype lpref in
        sub S' lmeth (fun S'' => run_error S'' native_error_type))

    end).

Definition to_primitive runs S C v (prefo : option preftype) : result :=
  match v with
  | value_prim w => out_ter S w
  | value_object l =>
    if_prim (object_default_value runs S C l prefo) res_ter
  end.

Definition to_number runs S C v : result :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_number w)
  | value_object l =>
    if_prim (to_primitive runs S C l (Some preftype_number)) (fun S1 w =>
      res_ter S1 (convert_prim_to_number w))
  end.

Definition to_integer runs S C v : result :=
  if_number (to_number runs S C v) (fun S1 n =>
    res_ter S1 (convert_number_to_integer n)).

Definition to_int32 runs S C v : specres int :=
  if_number (to_number runs S C v) (fun S' n =>
    res_spec S' (JsNumber.to_int32 n)).

Definition to_uint32 runs S C v : specres int :=
  if_number (to_number runs S C v) (fun S' n =>
    res_spec S' (JsNumber.to_uint32 n)).

Definition to_string runs S C v : result :=
  match v with
  | value_prim w =>
    out_ter S (convert_prim_to_string w)
  | value_object l =>
    if_prim (to_primitive runs S C l (Some preftype_string)) (fun S1 w =>
      res_ter S1 (convert_prim_to_string w))
  end.


(**************************************************************)
(** Built-in constructors *)

Definition call_object_new S v : result :=
  match type_of v with
  | type_object => out_ter S v
  | type_string | type_bool | type_number =>
    to_object S v
  | type_null | type_undef =>
    'let O := object_new prealloc_object_proto "Object" in
    'let p := object_alloc S O in (* LATER: ['let] on pairs *)
    let '(l, S') := p in
    out_ter S' l
  end.

Definition bool_proto_value_of_call S vthis : result :=
  if_some (run_value_viewable_as_prim "Boolean" S vthis) (fun vw =>
    match vw return result with
    | Some (prim_bool b) => out_ter S b
    | _ => run_error S native_error_type
    end).

Definition run_construct_prealloc runs S C B (args : list value) : result :=
  match B with

  | prealloc_object =>
    'let v := get_arg 0 args in
    call_object_new S v

  | prealloc_function =>
    result_not_yet_implemented (* LATER:  Waiting for specification *)

  | prealloc_bool =>
    'let v := get_arg 0 args in
    'let b := convert_value_to_boolean v in
    'let O1 := object_new prealloc_bool_proto "Boolean" in
    'let O := object_with_primitive_value O1 b in
    'let p := object_alloc S O in (* LATER: ['let] on pair *)
    let '(l, S') := p in
    out_ter S' l

  | prealloc_number =>
    'let follow := fun S' v =>
      'let O1 := object_new prealloc_number_proto "Number" in
      'let O := object_with_primitive_value O1 v in
      let '(l, S1) := object_alloc S' O in
      out_ter S1 l : result
      in
    ifb args = nil then
      follow S JsNumber.zero
    else
      'let v := get_arg 0 args in
      if_number (to_number runs S C v) follow

  | prealloc_array =>
    'let O := object_new prealloc_array_proto "Array" in
    'let p := object_alloc S O in
    let '(l, S') := p in
    if_not_throw (object_define_own_prop runs S' C l "length" (attributes_data_intro JsNumber.zero true true true) throw_false) (fun S _ =>
      out_ter S l)

  | prealloc_string =>
    result_not_yet_implemented (* LATER:  Waiting for specification *)

  | prealloc_error =>
    'let v := get_arg 0 args in
    build_error S prealloc_error_proto v

  | prealloc_native_error ne =>
    'let v := get_arg 0 args in
    build_error S (prealloc_native_error ne) v

  | prealloc_native_error_proto ne =>
    'let v := get_arg 0 args in
    build_error S B v

  | _ => (* NOTE:  Are there other cases missing? *)
    impossible_with_heap_because S "Missing case in [run_construct_prealloc]."

  end.

Definition run_construct_default runs S C l args :=
  if_value (run_object_get runs S C l "prototype") (fun S1 v1 =>
    'let vproto :=
      ifb type_of v1 = type_object then v1
      else prealloc_object_proto
      in
    'let O := object_new vproto "Object" in
    'let p := object_alloc S1 O in (* LATER: ['let] on pair *)
    let '(l', S2) := p in
    if_value (runs_type_call runs S2 C l l' args) (fun S3 v2 =>
      'let vr := ifb type_of v2 = type_object then v2 else l' in
      res_ter S3 vr)).

Definition run_construct runs S C co l args : result :=
  match co with
  | construct_default =>
    run_construct_default runs S C l args
  | construct_prealloc B =>
    run_construct_prealloc runs S C B args
  | construct_after_bind =>
    impossible_with_heap_because S "[construct_after_bind] received in [run_construct]."
  end.


(**************************************************************)
(** Function Calls *)

Definition run_call_default runs S C (lf : object_loc) : result :=
  'let default := (out_ter S undef : result) in
  if_some (run_object_method object_code_ S lf) (fun OC =>
       match OC with
       | None => default
       | Some bd =>
         ifb funcbody_empty bd then
           default
         else
           if_success_or_return (runs_type_prog runs S C (funcbody_prog bd))
             (fun S' => out_ter S' undef) (* normal *)
             (fun S' rv => out_ter S' rv) (* return *)
       end).

Definition creating_function_object_proto runs S C l : result :=
  if_object (run_construct_prealloc runs S C prealloc_object nil) (fun S1 lproto =>
    'let A1 := attributes_data_intro l true false true in
    if_bool (object_define_own_prop runs S1 C lproto "constructor" A1 false) (fun S2 b =>
      'let A2 := attributes_data_intro lproto true false false in
      object_define_own_prop runs S2 C l "prototype" A2 false)).

Definition creating_function_object runs S C (names : list string) (bd : funcbody) X str : result :=
  'let O := object_new prealloc_function_proto "Function" in
  'let O1 := object_with_get O builtin_get_function in
  'let O2 := object_with_invokation O1
    (Some construct_default)
    (Some call_default)
    (Some builtin_has_instance_function) in
  'let O3 := object_with_details O2 (Some X) (Some names) (Some bd) None None None None in
  'let p := object_alloc S O3 in (* LATER: ['let] on pairs *)
  let '(l, S1) := p in
  'let A1 := attributes_data_intro (JsNumber.of_int (length names)) false false false in
  if_bool (object_define_own_prop runs S1 C l "length" A1 false) (fun S2 b2 =>
    if_bool (creating_function_object_proto runs S2 C l) (fun S3 b3 =>
      if negb str then res_ter S3 l
      else (
        'let vthrower := value_object prealloc_throw_type_error in
        'let A2 := attributes_accessor_intro vthrower vthrower false false in
        if_bool (object_define_own_prop runs S3 C l "caller" A2 false) (fun S4 b4 =>
          if_bool (object_define_own_prop runs S4 C l "arguments" A2 false) (fun S5 b5 =>
            res_ter S5 l))))).

Fixpoint binding_inst_formal_params runs S C L (args : list value) (names : list string) str {struct names} : result_void :=
  match names with
  | nil => res_void S
  | argname :: names' =>
    'let v := hd undef args in
    'let args' := tl args in
    if_bool (env_record_has_binding runs S C L argname) (fun S1 hb =>
      'let follow := fun S' =>
        if_void (env_record_set_mutable_binding runs S' C L argname v str) (fun S'' =>
          binding_inst_formal_params runs S'' C L args' names' str)
        in
      if hb then
        follow S1
      else
        if_void (env_record_create_mutable_binding runs S1 C L argname None) follow)
  end.

Fixpoint binding_inst_function_decls runs S C L (fds : list funcdecl) str bconfig {struct fds} : result_void :=
  match fds with
  | nil => res_void S
  | fd :: fds' =>
      'let fbd := funcdecl_body fd in
      'let str_fd := funcbody_is_strict fbd in
      'let fparams := funcdecl_parameters fd in
      'let fname := funcdecl_name fd in
      if_object (creating_function_object runs S C fparams fbd (execution_ctx_variable_env C) str_fd) (fun S1 fo =>
        'let follow := fun S2 =>
          if_void (env_record_set_mutable_binding runs S2 C L fname fo str) (fun S3 =>
            binding_inst_function_decls runs S3 C L fds' str bconfig)
          in
        if_bool (env_record_has_binding runs S1 C L fname) (fun S2 has =>
          if has then (
            ifb L = env_loc_global_env_record then (
              if_spec (run_object_get_prop runs S2 C prealloc_global fname) (fun S3 D =>
                match D with
                | full_descriptor_undef =>
                  impossible_with_heap_because S3 "Undefined full descriptor in [binding_inst_function_decls]."
                | full_descriptor_some A =>
                  ifb attributes_configurable A then (
                    'let A' := attributes_data_intro undef true true bconfig in
                    if_bool (object_define_own_prop runs S3 C prealloc_global fname A' true)
                      (fun S _ => follow S)
                  ) else ifb descriptor_is_accessor A
                    \/ attributes_writable A = false \/ attributes_enumerable A = false then
                      run_error S3 native_error_type
                  else
                    follow S3
                end)
            ) else follow S2)
          else
            if_void (env_record_create_mutable_binding runs S2 C L fname (Some bconfig)) follow))
  end.

Definition make_arg_getter runs S C x X : result :=
  let xbd := "return " ++ x ++ ";" in
  let bd := funcbody_intro
              (prog_intro true ((element_stat (stat_return
                (Some (expr_identifier x))))::nil)) xbd in
  creating_function_object runs S C nil bd X true.

Definition make_arg_setter runs S C x X : result :=
  let xparam := x ++ "_arg" in
  let xbd := x ++ " = " ++ xparam ++ ";" in
  let bd := funcbody_intro
              (prog_intro true ((element_stat
                (expr_assign (expr_identifier x) None (expr_identifier xparam)))::nil)) xbd in
  creating_function_object runs S C (xparam::nil) bd X true.

Fixpoint arguments_object_map_loop runs S C l xs len args X str lmap xsmap {struct len} : result_void :=
  (* [len] should always be [length args]. *)
  match len with
  | O => (* args = nil *)
    ifb xsmap = nil then
      res_void S
    else (
      if_some (pick_option (object_binds S l)) (fun O =>
        'let O' := object_for_args_object O lmap builtin_get_args_obj
                    builtin_get_own_prop_args_obj builtin_define_own_prop_args_obj
                    builtin_delete_args_obj in
        res_void (object_write S l O')))
  | S len' => (* args <> nil *)
    'let tdl := LibList.take_drop_last args in let (rmlargs, largs) := tdl in
    'let arguments_object_map_loop' := fun S xsmap =>
      arguments_object_map_loop runs S C l xs len' rmlargs X str lmap xsmap in
    'let A := attributes_data_intro_all_true largs in
    if_bool (object_define_own_prop runs S C l (convert_prim_to_string len') A false) (fun S1 b =>
      ifb len' >= length xs then
        arguments_object_map_loop' S1 xsmap
      else (
        let dummy := "" in
        'let x := nth_def dummy len' xs in
        ifb str = true \/ Mem x xsmap then
          arguments_object_map_loop' S1 xsmap
        else
          if_object (make_arg_getter runs S1 C x X) (fun S2 lgetter =>
            if_object (make_arg_setter runs S2 C x X) (fun S3 lsetter =>
              'let A' := attributes_accessor_intro (value_object lgetter) (value_object lsetter) false true in
              if_bool (object_define_own_prop runs S3 C lmap (convert_prim_to_string len') A' false) (fun S4 b' =>
                arguments_object_map_loop' S4 (x :: xsmap)))))
      )
  end.

Definition arguments_object_map runs S C l xs args X str : result_void :=
  if_object (run_construct_prealloc runs S C prealloc_object nil) (fun S' lmap =>
    arguments_object_map_loop runs S' C l xs (length args) args X str lmap nil).

Definition create_arguments_object runs S C lf xs args X str : result :=
  'let O := object_create_builtin prealloc_object_proto "Arguments" Heap.empty in
  'let p := object_alloc S O in
  let '(l, S') := p in (* LATER: ['let] on pair *)
  'let A := attributes_data_intro (JsNumber.of_int (length args)) true false true in
  if_bool (object_define_own_prop runs S' C l "length" A false) (fun S1 b =>
    if_void (arguments_object_map runs S1 C l xs args X str) (fun S2 =>
      if str then (
        'let vthrower := value_object prealloc_throw_type_error in
        'let A := attributes_accessor_intro vthrower vthrower false false in
        if_bool (object_define_own_prop runs S2 C l "caller" A false) (fun S3 b' =>
          if_bool (object_define_own_prop runs S3 C l "callee" A false) (fun S4 b'' =>
            res_ter S4 l))
      ) else (
        'let A := attributes_data_intro (value_object lf) true false true in
        if_bool (object_define_own_prop runs S2 C l "callee" A false) (fun S3 b' =>
          res_ter S3 l)))).

Definition binding_inst_arg_obj runs S C lf p xs args L : result_void :=
  let arguments := "arguments" in
  'let str := prog_intro_strictness p in
    if_object (create_arguments_object runs S C lf xs args
                   (execution_ctx_variable_env C) str) (fun S1 largs =>
      if str then
        if_void (env_record_create_immutable_binding S1 L arguments) (fun S2 =>
          env_record_initialize_immutable_binding S2 L arguments largs)
      else
        env_record_create_set_mutable_binding runs S1 C L arguments None largs false).

Fixpoint binding_inst_var_decls runs S C L (vds : list string) bconfig str : result_void :=
  match vds with
  | nil => res_void S
  | vd :: vds' =>
    'let bivd := fun S => binding_inst_var_decls runs S C L vds' bconfig str in
    if_bool (env_record_has_binding runs S C L vd) (fun S1 has =>
      if has then
        bivd S1
      else
        if_void (env_record_create_set_mutable_binding runs S1 C L vd (Some bconfig) undef str) bivd)
  end.

Definition execution_ctx_binding_inst runs S C (ct : codetype) (funco : option object_loc) p (args : list value) : result_void :=
  match execution_ctx_variable_env C with
  | nil => impossible_with_heap_because S
    "Empty [execution_ctx_variable_env] in [execution_ctx_binding_inst]."
  | L::_ =>
    'let str := prog_intro_strictness p in
    'let follow := fun S' names =>
      'let bconfig := decide (ct = codetype_eval) in
      'let fds := prog_funcdecl p in
      if_void (binding_inst_function_decls runs S' C L fds str bconfig) (fun S1 =>
        if_bool (env_record_has_binding runs S1 C L "arguments") (fun S2 bdefined =>
          'let follow2 := fun S' =>
            let vds := prog_vardecl p in
            binding_inst_var_decls runs S' C L vds bconfig str
            in
          match ct, funco, bdefined with
          | codetype_func, Some func, false =>
            if_void (binding_inst_arg_obj runs S2 C func p names args L) follow2
          | codetype_func, _, false =>
            impossible_with_heap_because S2 "Weird `arguments' object in [execution_ctx_binding_inst]."
          | _, _, _ => follow2 S2
          end))
      in
    match ct, funco with
      | codetype_func, Some func =>
        if_some (run_object_method object_formal_parameters_ S func) (fun nameso =>
          if_some nameso (fun names =>
            if_void (binding_inst_formal_params runs S C L args names str) (fun S' =>
              follow S' names)))
      | codetype_func, _ =>
        impossible_with_heap_because S "Non coherent functionnal code type in [execution_ctx_binding_inst]."
      | _, None => follow S nil
      | _, _ =>
        impossible_with_heap_because S "Non coherent non-functionnal code type in [execution_ctx_binding_inst]."
    end
  end.

Definition entering_func_code runs S C lf vthis (args : list value) : result :=
  if_some (run_object_method object_code_ S lf) (fun bdo =>
    if_some bdo (fun bd =>
      'let str := funcbody_is_strict bd in
      'let follow := fun S' vthis' =>
        if_some (run_object_method object_scope_ S' lf) (fun lexo =>
          if_some lexo (fun lex =>
            'let p := lexical_env_alloc_decl S' lex in
            let '(lex', S1) := p in
            'let C' := execution_ctx_intro_same lex' vthis' str in
            if_void (execution_ctx_binding_inst runs S1 C' codetype_func (Some lf) (funcbody_prog bd) args) (fun S2 =>
            run_call_default runs S2 C' lf)))
        in
      if str then
        follow S vthis
      else
        match vthis with
        | value_object lthis => follow S vthis
        | null => follow S prealloc_global
        | undef => follow S prealloc_global
        | value_prim _ => if_value (to_object S vthis) follow
        end)).

(**************************************************************)

Definition run_object_get_own_prop runs S C l x : specres full_descriptor :=
  if_some (run_object_method object_get_own_prop_ S l) (fun B =>
    'let default := fun S' =>
      if_some (run_object_method object_properties_ S' l) (fun P =>
        res_spec S' (
          if_some_or_default (convert_option_attributes (Heap.read_option P x))
            (full_descriptor_undef) id)) in
    match B with
      | builtin_get_own_prop_default =>
        default S
      | builtin_get_own_prop_args_obj =>
        if_spec (default S) (fun S1 D =>
          match D with
          | full_descriptor_undef =>
            res_spec S1 full_descriptor_undef
          | full_descriptor_some A =>
            if_some (run_object_method object_parameter_map_ S1 l) (fun lmapo =>
              if_some lmapo (fun lmap =>
                if_spec (runs_type_object_get_own_prop runs S1 C lmap x) (fun S2 D =>
                  'let follow := fun S' A =>
                    res_spec S' (full_descriptor_some A) in
                  match D with
                     | full_descriptor_undef =>
                       follow S2 A
                     | full_descriptor_some Amap =>
                       if_value (run_object_get runs S2 C lmap x) (fun S3 v =>
                         match A with
                         | attributes_data_of Ad =>
                           follow S3 (attributes_data_with_value Ad v)
                         | attributes_accessor_of Aa =>
                           impossible_with_heap_because S3 "[run_object_get_own_prop]:  received an accessor property descriptor in a point where the specification suppose it never happens."
                         end)
                     end)))
          end)
      | builtin_get_own_prop_string =>
        if_spec (default S) (fun S D =>
          match D with
          | full_descriptor_some _ =>
            res_spec S D
          | full_descriptor_undef =>
            if_spec (to_int32 runs S C x) (fun S k =>
              if_string (runs_type_to_string runs S C (abs k)) (fun S s =>
                ifb x <> s
                then res_spec S full_descriptor_undef
                else if_string (run_object_prim_value S l) (fun S (str : string) =>
                       if_spec (to_int32 runs S C x) (fun S k => (* This actually cannot change the heap of return a different result than the first time... but this is closer to eyeball closesness than not computing it twice. *)
                         'let len := Z.of_nat (String.length str) in
                         let idx := k in
                         ifb len <= idx
                         then res_spec S full_descriptor_undef
                         else let resultStr := string_sub str idx 1 in
                              let A := attributes_data_intro resultStr false true false in
                              res_spec S (full_descriptor_some A)))))
          end)
      end).

Definition run_function_has_instance runs S lv vo : result :=
  (* Corresponds to the [spec_function_has_instance_1] of the specification.] *)
  match vo with
  | value_prim _ =>
    run_error S native_error_type
  | value_object lo =>
    if_some (run_object_method object_proto_ S lv) (fun vproto =>
      match vproto with
      | null =>
        res_ter S false
      | value_object proto =>
        ifb proto = lo then
          res_ter S true
        else
          runs_type_function_has_instance runs S proto lo
      | value_prim _ =>
        impossible_with_heap_because S "Primitive found in the prototype chain in [run_object_has_instance_loop]."
      end)
  end.


Definition run_object_has_instance runs B S C l v : result :=
  match B with

  | builtin_has_instance_function =>
    match v with
    | value_prim w => out_ter S false
    | value_object lv =>
      if_value (run_object_get runs S C l "prototype") (fun S1 vproto =>
        match vproto return result with
        | value_object lproto =>
           runs_type_function_has_instance runs S1 lv lproto
        | value_prim _ =>
           run_error S1 native_error_type
        end)
    end

  | builtin_has_instance_after_bind =>
    result_not_yet_implemented (* LATER:  Waiting for the specification *)

  end.



(**************************************************************)

Definition from_prop_descriptor runs S C D : result :=
  match D with
  | full_descriptor_undef => out_ter S undef
  | full_descriptor_some A =>
    if_object (run_construct_prealloc runs S C prealloc_object nil) (fun S1 l =>
      'let follow := fun S0 _ =>
        'let A1 := attributes_data_intro_all_true (attributes_enumerable A) in
        if_bool (object_define_own_prop runs S0 C l "enumerable" (descriptor_of_attributes A1) throw_false) (fun S0' _ =>
          'let A2 := attributes_data_intro_all_true (attributes_configurable A) in
          if_bool (object_define_own_prop runs S0' C l "configurable" (descriptor_of_attributes A2) throw_false) (fun S' _ =>
            res_ter S' l))
        in
      match A with
      | attributes_data_of Ad =>
        'let A1 := attributes_data_intro_all_true (attributes_data_value Ad) in
        if_bool (object_define_own_prop runs S1 C l "value" (descriptor_of_attributes A1) throw_false) (fun S2 _ =>
          'let A2 := attributes_data_intro_all_true (attributes_data_writable Ad) in
          if_bool (object_define_own_prop runs S2 C l "writable" (descriptor_of_attributes A2) throw_false) follow)
      | attributes_accessor_of Aa =>
        'let A1 := attributes_data_intro_all_true (attributes_accessor_get Aa) in
        if_bool (object_define_own_prop runs S1 C l "get" (descriptor_of_attributes A1) throw_false) (fun S2 _ =>
          'let A2 := attributes_data_intro_all_true (attributes_accessor_set Aa) in
          if_bool (object_define_own_prop runs S2 C l "set" (descriptor_of_attributes A2) throw_false) follow)
      end)
  end.


End LexicalEnvironments.

Implicit Type runs : runs_type.
Implicit Arguments run_error [[T]].


Section Operators.

(**************************************************************)
(** Operators *)

Definition is_lazy_op (op : binary_op) : option bool :=
  match op with
  | binary_op_and => Some false
  | binary_op_or => Some true
  | _ => None
  end.

Definition get_puremath_op (op : binary_op) : option (number -> number -> number) :=
  match op with
  | binary_op_mult => Some JsNumber.mult
  | binary_op_div => Some JsNumber.div
  | binary_op_mod => Some JsNumber.fmod
  | binary_op_sub => Some JsNumber.sub
  | _ => None
  end.

Definition get_inequality_op (op : binary_op) : option (bool * bool) :=
  match op with
  | binary_op_lt => Some (false, false)
  | binary_op_gt => Some (true, false)
  | binary_op_le => Some (true, true)
  | binary_op_ge => Some (false, true)
  | _ => None
  end.

Definition get_shift_op (op : binary_op) : option (bool * (int -> int -> int)) :=
  match op with
  | binary_op_left_shift => Some (false, JsNumber.int32_left_shift)
  | binary_op_right_shift => Some (false, JsNumber.int32_right_shift)
  | binary_op_unsigned_right_shift => Some (true, JsNumber.uint32_right_shift)
  | _ => None
  end.

Definition get_bitwise_op (op : binary_op) : option (int -> int -> int) :=
  match op with
  | binary_op_bitwise_and => Some JsNumber.int32_bitwise_and
  | binary_op_bitwise_or => Some JsNumber.int32_bitwise_or
  | binary_op_bitwise_xor => Some JsNumber.int32_bitwise_xor
  | _ => None
  end.


Definition run_equal runs S C v1 v2 : result :=
  let conv_number := fun S v =>
    to_number runs S C v in
  let conv_primitive := fun S v =>
    to_primitive runs S C v None in
  'let checkTypesThen := fun S0 v1 v2 (K : type -> type -> result) =>
    let ty1 := type_of v1 in
    let ty2 := type_of v2 in
    ifb ty1 = ty2 then
      out_ter S0 (equality_test_for_same_type ty1 v1 v2) : result
    else K ty1 ty2 in
  checkTypesThen S v1 v2 (fun ty1 ty2 =>
    'let dc_conv := fun v1 F v2 =>
      if_value (F S v2) (fun S0 v2' =>
        runs_type_equal runs S0 C v1 v2') in
    let so b : result :=
      out_ter S b in
    ifb (ty1 = type_null /\ ty2 = type_undef) then
      so true
    else ifb (ty1 = type_undef /\ ty2 = type_null) then
      so true
    else ifb ty1 = type_number /\ ty2 = type_string then
      dc_conv v1 conv_number v2
    else ifb ty1 = type_string /\ ty2 = type_number then
      dc_conv v2 conv_number v1
    else ifb ty1 = type_bool then
      dc_conv v2 conv_number v1
    else ifb ty2 = type_bool then
      dc_conv v1 conv_number v2
    else ifb (ty1 = type_string \/ ty1 = type_number) /\ ty2 = type_object then
      dc_conv v1 conv_primitive v2
    else ifb ty1 = type_object /\ (ty2 = type_string \/ ty2 = type_number) then
      dc_conv v2 conv_primitive v1
    else so false).


Definition convert_twice T T0
    (ifv : resultof T0 -> (state -> T -> specres (T * T)) -> specres (T * T))
    (KC : state -> value -> resultof T0) S v1 v2 : specres (T * T) :=
  ifv (KC S v1) (fun S1 vc1 =>
    ifv (KC S1 v2) (fun S2 vc2 =>
      res_spec S2 (vc1, vc2))).

Definition convert_twice_primitive runs S C v1 v2 :=
  convert_twice (@if_prim (prim * prim)) (fun S v => to_primitive runs S C v None) S v1 v2.

Definition convert_twice_number runs S C v1 v2 :=
  convert_twice (@if_number (number * number)) (fun S v => to_number runs S C v) S v1 v2.

Definition convert_twice_string runs S C v1 v2 :=
  convert_twice (@if_string (string * string)) (fun S v => to_string runs S C v) S v1 v2.



Definition issome T (ot:option T) :=
  match ot with
  | Some _ => true
  | _ => false
  end.

Definition run_binary_op runs S C (op : binary_op) v1 v2 : result :=

  ifb op = binary_op_add then
    if_spec (convert_twice_primitive runs S C v1 v2) ((fun S1 ww => let '(w1,w2) := ww in
      ifb type_of w1 = type_string \/ type_of w2 = type_string then
        if_spec (convert_twice_string runs S1 C w1 w2) ((fun S2 ss => let '(s1,s2) := ss in
          res_out (out_ter S2 (s1 ++ s2))))
        else
          if_spec (convert_twice_number runs S1 C w1 w2) ((fun S2 nn => let '(n1,n2) := nn in
            res_out (out_ter S2 (JsNumber.add n1 n2))))))
  else if issome (get_puremath_op op) then
    if_some (get_puremath_op op) (fun mop =>
      if_spec (convert_twice_number runs S C v1 v2) ((fun S1 nn => let '(n1,n2) := nn in
        res_out (out_ter S1 (mop n1 n2)))))

  else if issome (get_shift_op op) then
    if_some (get_shift_op op) (fun so =>
      let '(b_unsigned, F) := so in
      if_spec ((if b_unsigned then to_uint32 else to_int32) runs S C v1) (fun S1 k1 =>
        if_spec (to_uint32 runs S1 C v2) (fun S2 k2 =>
          let k2' := JsNumber.modulo_32 k2 in
          res_ter S2 (JsNumber.of_int (F k1 k2')))))

  else if issome (get_bitwise_op op) then
    if_some (get_bitwise_op op) (fun bo =>
      if_spec (to_int32 runs S C v1) (fun S1 k1 =>
        if_spec (to_int32 runs S1 C v2) (fun S2 k2 =>
          res_ter S2 (JsNumber.of_int (bo k1 k2)))))

  else if issome (get_inequality_op op) then
    if_some (get_inequality_op op) (fun io =>
      let '(b_swap, b_neg) :=  io in
      if_spec (convert_twice_primitive runs S C v1 v2) ((fun S1 ww => let '(w1,w2) := ww in
        'let p := if b_swap then (w2, w1) else (w1, w2) in
        let '(wa, wb) := p in (* LATER: ['let] on pair*)
        let wr := inequality_test_primitive wa wb in
        res_out (out_ter S1 (ifb wr = prim_undef then false
          else ifb b_neg = true /\ wr = true then false
          else ifb b_neg = true /\ wr = false then true
          else wr)))))

  else ifb op = binary_op_instanceof then
    match v2 with
    | value_object l =>
      if_some (run_object_method object_has_instance_ S l) (fun B =>
        option_case (fun _ => run_error S native_error_type : result)
        (fun has_instance_id _ =>
          run_object_has_instance runs has_instance_id S C l v1)
        B tt)
    | value_prim _ => run_error S native_error_type
    end

  else ifb op = binary_op_in then
    match v2 with
    | value_object l =>
      if_string (to_string runs S C v1) (fun S2 x =>
        object_has_prop runs S2 C l x)
    | value_prim _ => run_error S native_error_type
    end

  else ifb op = binary_op_equal then
    runs_type_equal runs S C v1 v2

  else ifb op = binary_op_disequal then
    if_bool (runs_type_equal runs S C v1 v2) (fun S0 b0 =>
      (res_ter S0 (negb b0)))

  else ifb op = binary_op_strict_equal then
    out_ter S (strict_equality_test v1 v2)

  else ifb op = binary_op_strict_disequal then
    out_ter S (negb (strict_equality_test v1 v2))

  else ifb op = binary_op_coma then
    out_ter S v2

  else (* binary_op_and | binary_op_or *)
    (* Lazy operators are already dealt with at this point. *)
    impossible_with_heap_because S "Undealt lazy operator in [run_binary_op].".


Definition run_prepost_op (op : unary_op) : option ((number -> number) * bool) :=
  match op with
  | unary_op_pre_incr => Some (add_one, true)
  | unary_op_pre_decr => Some (sub_one, true)
  | unary_op_post_incr => Some (add_one, false)
  | unary_op_post_decr => Some (sub_one, false)
  | _ => None
  end.

Definition run_typeof_value S v :=
  match v with
  | value_prim w => typeof_prim w
  | value_object l => ifb is_callable S l then "function" else "object"
  end.

Definition run_unary_op runs S C (op : unary_op) e : result :=
  ifb prepost_unary_op op then
    if_success (runs_type_expr runs S C e) (fun S1 rv1 =>
      if_spec (ref_get_value runs S1 C rv1) (fun S2 v2 =>
        if_number (to_number runs S2 C v2) (fun S3 n1 =>
          if_some (run_prepost_op op) (fun po =>
            let '(number_op, is_pre) := po in
            'let n2 := number_op n1 in
            'let v := prim_number (if is_pre then n2 else n1) in
            if_void (ref_put_value runs S3 C rv1 n2) (fun S4 =>
              out_ter S4 v)))))
  else
    match op with

    | unary_op_delete =>
      if_success (runs_type_expr runs S C e) (fun S rv =>
        match rv with
        | resvalue_ref r =>
          ifb ref_is_unresolvable r then (
            if ref_strict r then
              run_error S native_error_syntax
            else res_ter S true
          ) else
            match ref_base r with
            | ref_base_type_value v =>
              if_object (to_object S v) (fun S l =>
                runs_type_object_delete runs S C l (ref_name r) (ref_strict r))
            | ref_base_type_env_loc L =>
              if ref_strict r then
                run_error S native_error_syntax
              else env_record_delete_binding runs S C L (ref_name r)
            end
        | _ => res_ter S true
        end)

    | unary_op_typeof =>
      if_success (runs_type_expr runs S C e) (fun S1 rv =>
        match rv with
        | resvalue_value v =>
          res_ter S1 (run_typeof_value S1 v)
        | resvalue_ref r =>
          ifb ref_is_unresolvable r then
            res_ter S1 "undefined"
          else
            if_spec (ref_get_value runs S1 C r) (fun S2 v =>
              res_ter S2 (run_typeof_value S2 v))
        | resvalue_empty => impossible_with_heap_because S1 "Empty result for a `typeof' in [run_unary_op]."
        end)

    | _ => (* Regular operators *)
      if_spec (run_expr_get_value runs S C e) (fun S1 v =>
        match op with

        | unary_op_void => res_ter S1 undef

        | unary_op_add => to_number runs S1 C v

        | unary_op_neg =>
          if_number (to_number runs S1 C v) (fun S2 n =>
            res_ter S2 (JsNumber.neg n))

        | unary_op_bitwise_not =>
          if_spec (to_int32 runs S1 C v) (fun S2 k =>
            res_ter S2 (JsNumber.of_int (JsNumber.int32_bitwise_not k)))

        | unary_op_not =>
          res_ter S1 (neg (convert_value_to_boolean v))

        | _ => impossible_with_heap_because S1 "Undealt regular operator in [run_unary_op]."

        end)

    end.

End Operators.


Section Interpreter.

(**************************************************************)
(** Some spec cases *)

Definition create_new_function_in runs S C args bd :=
  creating_function_object runs S C args bd (execution_ctx_lexical_env C) (execution_ctx_strict C).

Fixpoint init_object runs S C l (pds : propdefs) {struct pds} : result :=
  match pds return result with
  | nil => out_ter S l
  | (pn, pb) :: pds' =>
    'let x := string_of_propname pn in
    'let follows := fun S1 A =>
      if_success (object_define_own_prop runs S1 C l x A false) (fun S2 rv =>
        init_object runs S2 C l pds') in
    match pb with
    | propbody_val e0 =>
      if_spec (run_expr_get_value runs S C e0) (fun S1 v0 =>
        let A := attributes_data_intro v0 true true true in
        follows S1 A)
    | propbody_get bd =>
      if_value (create_new_function_in runs S C nil bd) (fun S1 v0 =>
        let A := attributes_accessor_intro v0 undef true true in
        follows S1 A)
    | propbody_set args bd =>
      if_value (create_new_function_in runs S C args bd) (fun S1 v0 =>
        let A := attributes_accessor_intro undef v0 true true in
        follows S1 A)
    end
  end.

Definition run_var_decl_item runs S C x eo : result :=
  match eo with
    | None => out_ter S x
    | Some e =>
      if_spec (identifier_resolution runs S C x) (fun S1 ir =>
        if_spec (run_expr_get_value runs S1 C e) (fun S2 v =>
          if_void (ref_put_value runs S2 C ir v) (fun S3 =>
            out_ter S3 x)))
  end.

Fixpoint run_var_decl runs S C xeos : result :=
  match xeos with
  | nil => out_ter S res_empty
  | (x, eo) :: xeos' =>
     if_value (run_var_decl_item runs S C x eo) (fun S1 vname =>
        run_var_decl runs S1 C xeos')
  end.

Fixpoint run_list_expr runs S1 C (vs : list value) (es : list expr) : specres (list value) :=
  match es with
  | nil =>
    res_spec S1 (rev vs)
  | e :: es' =>
    if_spec (run_expr_get_value runs S1 C e) (fun S2 v =>
      run_list_expr runs S2 C (v :: vs) es')
  end.

Fixpoint run_block runs S C (ts_rev : list stat) : result :=
  match ts_rev with
  | nil =>
    res_ter S resvalue_empty
  | t :: ts_rev' =>
    if_success (run_block runs S C ts_rev') (fun S0 rv0 =>
      if_success_state rv0 (runs_type_stat runs S0 C t) out_ter)
  end.


(**************************************************************)
(** ** Intermediary functions for all non-trivial cases. *)

Definition run_expr_binary_op runs S C op e1 e2 : result :=
  match is_lazy_op op with
  | None =>
    if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
      if_spec (run_expr_get_value runs S1 C e2) (fun S2 v2 =>
        run_binary_op runs S2 C op v1 v2))
  | Some b_ret =>
    if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
      'let b1 := convert_value_to_boolean v1 in
      ifb b1 = b_ret then res_ter S1 v1
      else
        if_spec (run_expr_get_value runs S1 C e2) (fun S2 v =>
          res_ter S2 v))
  end.

Definition run_expr_access runs S C e1 e2 : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
    if_spec (run_expr_get_value runs S1 C e2) (fun S2 v2 =>
      ifb v1 = prim_undef \/ v1 = prim_null then
        run_error S2 native_error_type
      else
        if_string (to_string runs S2 C v2) (fun S3 x =>
          res_ter S3 (ref_create_value v1 x (execution_ctx_strict C))))).

Definition run_expr_assign runs S C (opo : option binary_op) e1 e2 : result :=
  if_success (runs_type_expr runs S C e1) (fun S1 rv1 =>
    'let follow := fun S rv' =>
      match rv' return result with
      | resvalue_value v =>
        if_void (ref_put_value runs S C rv1 v) (fun S' =>
         out_ter S' v)
      | _ => impossible_with_heap_because S "Non-value result in [run_expr_assign]."
      end in
    match opo with
    | None =>
      if_spec (run_expr_get_value runs S1 C e2) follow
    | Some op =>
      if_spec (ref_get_value runs S1 C rv1) (fun S2 v1 =>
        if_spec (run_expr_get_value runs S2 C e2) (fun S3 v2 =>
          if_success (run_binary_op runs S3 C op v1 v2) follow))
    end).

Definition run_expr_function runs S C fo args bd : result :=
  match fo with
  | None =>
    let lex := execution_ctx_lexical_env C in
    creating_function_object runs S C args bd lex (funcbody_is_strict bd)
  | Some fn =>
    'let p := lexical_env_alloc_decl S (execution_ctx_lexical_env C) in (* LATER:  ['let] on pair *)
    let '(lex', S') := p in
    let follow L :=
      if_some (pick_option (env_record_binds S' L)) (fun E =>
        if_void (env_record_create_immutable_binding S' L fn) (fun S1 =>
          if_object (creating_function_object runs S1 C args bd lex' (funcbody_is_strict bd)) (fun S2 l =>
            if_void (env_record_initialize_immutable_binding S2 L fn l) (fun S3 =>
              out_ter S3 l)))) in
    destr_list lex' (fun _ =>
      impossible_with_heap_because S' "Empty lexical environnment allocated in [run_expr_function].")
      (fun L _ => follow L) tt
  end.


Definition entering_eval_code runs S C direct bd K : result :=
  'let str := (funcbody_is_strict bd) || (direct && execution_ctx_strict C) in
  'let C' := if direct then C else execution_ctx_initial str in
  'let p :=
    if str
      then lexical_env_alloc_decl S (execution_ctx_lexical_env C')
      else (execution_ctx_lexical_env C', S)
   in
  let '(lex, S') := p in (* LATER: ['let] on pair *)
  'let C1 :=
    if str
      then execution_ctx_with_lex_same C' lex
      else C'
    in
  'let p := funcbody_prog bd in
  if_void (execution_ctx_binding_inst runs S' C1 codetype_eval None p nil) (fun S1 =>
    K S1 C1).

Definition run_eval runs S C (is_direct_call : bool) (vs : list value) : result := (* Corresponds to the rule [spec_call_global_eval] of the specification. *)
  match get_arg 0 vs with
  | prim_string s =>
    match pick (parse s) with
    | None =>
      run_error S native_error_syntax
    | Some p =>
      entering_eval_code runs S C is_direct_call (funcbody_intro p s) (fun S1 C' =>
        if_ter (runs_type_prog runs S1 C' p) (fun S2 R =>
          match res_type R with
          | restype_throw =>
            res_ter S2 (res_throw (res_value R))
          | restype_normal =>
             if_empty_label S2 R (fun _ =>
              match res_value R with
              | resvalue_value v =>
                res_ter S2 v
              | resvalue_empty =>
                res_ter S2 undef
              | resvalue_ref r =>
                impossible_with_heap_because S2 "Reference found in the result of an `eval' in [run_eval]."
              end)
          | _ => impossible_with_heap_because S2 "Forbidden result type returned by an `eval' in [run_eval]."
          end))
    end
  | v => out_ter S v
  end.


Definition run_expr_call runs S C e1 e2s : result :=
  'let is_eval_direct := is_syntactic_eval e1 in
  if_success (runs_type_expr runs S C e1) (fun S1 rv =>
    if_spec (ref_get_value runs S1 C rv) (fun S2 f =>
      if_spec (run_list_expr runs S2 C nil e2s) (fun S3 vs =>
        match f with
        | value_object l =>
          (* LATER: restore the negation:
          ifb ~ (is_callable S3 l) then run_error S3 native_error_type
          else
          *)
          ifb (is_callable S3 l) then
            'let follow := fun vthis =>
              ifb l = prealloc_global_eval then
                run_eval runs S3 C is_eval_direct vs
              else runs_type_call runs S3 C l vthis vs in
            match rv with
            | resvalue_value v => follow undef
            | resvalue_ref r =>
              match ref_base r with
              | ref_base_type_value v =>
                ifb ref_is_property r then follow v
                else impossible_with_heap_because S3 "[run_expr_call] unable to call a non-property function."
              | ref_base_type_env_loc L =>
                if_some (env_record_implicit_this_value S3 L) follow
              end
            | resvalue_empty => impossible_with_heap_because S3 "[run_expr_call] unable to call an  empty result."
            end
           (* LATER: restore the negation by removing this *)
           else run_error S3 native_error_type
        | value_prim _ => run_error S3 native_error_type
        end))).

Definition run_expr_conditionnal runs S C e1 e2 e3 : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
    'let b := convert_value_to_boolean v1 in
    'let e := if b then e2 else e3 in
    if_spec (run_expr_get_value runs S1 C e) res_ter).

Definition run_expr_new runs S C e1 (e2s : list expr) : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v =>
    if_spec (run_list_expr runs S1 C nil e2s) (fun S2 args =>
      match v with
      | value_object l =>
        if_some (run_object_method object_construct_ S2 l) (fun coo =>
          match coo with
          | None => run_error S2 native_error_type
          | Some co => run_construct runs S2 C co l args
          end)
      | value_prim _ =>
        run_error S2 native_error_type
      end)).


(**************************************************************)

Definition run_stat_label runs S C lab t : result :=
  if_break (runs_type_stat runs S C t) (fun S1 R1 =>
    out_ter S1
      (ifb res_label R1 = lab then res_value R1 else R1)).

Definition run_stat_with runs S C e1 t2 : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
    if_object (to_object S1 v1) (fun S2 l =>
      'let lex := execution_ctx_lexical_env C in
      'let p := lexical_env_alloc_object S2 lex l provide_this_true in
      let '(lex', S3) := p in (* LATER: ['let] on pair *)
      'let C' := execution_ctx_with_lex C lex' in
      runs_type_stat runs S3 C' t2)).

Definition run_stat_if runs S C e1 t2 to : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
    'let b := convert_value_to_boolean v1 in
    if b then
      runs_type_stat runs S1 C t2
    else
      match to with
      | Some t3 =>
        runs_type_stat runs S1 C t3
      | None =>
        out_ter S1 resvalue_empty
      end).

Definition run_stat_while runs S C rv labs e1 t2 : result :=
  if_spec (run_expr_get_value runs S C e1) (fun S1 v1 =>
    'let b := convert_value_to_boolean v1 in
    if b then
      if_ter (runs_type_stat runs S1 C t2) (fun S2 R =>
        'let rv' := ifb res_value R <> resvalue_empty then res_value R else rv in
        'let loop := fun _ => runs_type_stat_while runs S2 C rv' labs e1 t2 in
        ifb res_type R <> restype_continue
             \/ ~ res_label_in R labs then (
           ifb res_type R = restype_break /\ res_label_in R labs then
              res_ter S2 rv'
           else (
              ifb res_type R <> restype_normal then
                res_ter S2 R
              else loop tt
           )
        ) else loop tt)
    else res_ter S1 rv).

Fixpoint run_stat_switch_end runs S C rv scs : result :=
  match scs with
  | nil =>
    out_ter S rv
  | switchclause_intro e ts :: scs' =>
    if_success_state rv (run_block runs S C (LibList.rev ts)) (fun S1 rv1 =>
      run_stat_switch_end runs S1 C rv1 scs')
  end.

Fixpoint run_stat_switch_no_default runs S C vi rv scs : result :=
  match scs with
  | nil =>
    out_ter S rv
  | switchclause_intro e ts :: scs' =>
    if_spec (run_expr_get_value runs S C e) (fun S1 v1 =>
      'let b := strict_equality_test v1 vi in
      if b then
        if_success (run_block runs S1 C (LibList.rev ts)) (fun S2 rv2 =>
          run_stat_switch_end runs S2 C rv2 scs')
      else
        run_stat_switch_no_default runs S1 C vi rv scs')
  end.

Definition run_stat_switch_with_default_default runs S C ts scs : result :=
  if_success (run_block runs S C (LibList.rev ts)) (fun S1 rv =>
    run_stat_switch_end runs S1 C rv scs).

Fixpoint run_stat_switch_with_default_B runs S C vi rv ts0 scs : result :=
  match scs with
  | nil =>
    run_stat_switch_with_default_default runs S C ts0 scs
  | switchclause_intro e ts :: scs' =>
    if_spec (run_expr_get_value runs S C e) (fun S1 v1 =>
      'let b := strict_equality_test v1 vi in
      if b then
        if_success (run_block runs S1 C (LibList.rev ts)) (fun S2 rv2 =>
          run_stat_switch_end runs S2 C rv2 scs')
      else
        run_stat_switch_with_default_B runs S1 C vi rv ts0 scs')
  end.

Fixpoint run_stat_switch_with_default_A runs S C found vi rv scs1 ts0 scs2 : result :=
  match scs1 with
  | nil =>
    if found then
      run_stat_switch_with_default_default runs S C ts0 scs2
    else
      run_stat_switch_with_default_B runs S C vi rv ts0 scs2
  | switchclause_intro e ts :: scs' =>
    'let follow := fun S =>
      if_success_state rv (run_block runs S C (LibList.rev ts)) (fun S1 rv0 =>
        run_stat_switch_with_default_A runs S1 C true vi rv0 scs' ts0 scs2)
      in
    if found then
      follow S
    else
      if_spec (run_expr_get_value runs S C e) (fun S1 v1 =>
        'let b := strict_equality_test v1 vi in
        if b then
          follow S1
        else
          run_stat_switch_with_default_A runs S1 C false vi rv scs' ts0 scs2)
  end.

Definition run_stat_switch runs S C labs e sb : result :=
  if_spec (run_expr_get_value runs S C e) (fun S1 vi =>
    'let follow := fun W =>
      if_success
        (if_break W (fun S2 R =>
           if res_label_in R labs then
             out_ter S2 (res_value R)
           else out_ter S2 R)) res_ter in
    match sb with
    | switchbody_nodefault scs =>
      follow (run_stat_switch_no_default runs S1 C vi resvalue_empty scs)
    | switchbody_withdefault scs1 ts scs2 =>
      follow (run_stat_switch_with_default_A runs S1 C false vi resvalue_empty scs1 ts scs2)
    end).

Definition run_stat_do_while runs S C rv labs e1 t2 : result :=
  if_ter (runs_type_stat runs S C t2) (fun S1 R =>
    'let rv' := ifb res_value R = resvalue_empty then rv else res_value R in
    'let loop := fun _ =>
      if_spec (run_expr_get_value runs S1 C e1) (fun S2 v1 =>
        'let b := convert_value_to_boolean v1 in
          if b then
            runs_type_stat_do_while runs S2 C rv' labs e1 t2
          else res_ter S2 rv') in
    ifb res_type R = restype_continue
         /\ res_label_in R labs then
      loop tt
    else
       ifb res_type R = restype_break /\ res_label_in R labs then
          res_ter S1 rv'
       else (
         ifb res_type R <> restype_normal then
           res_ter S1 R
         else loop tt)).

Definition run_stat_try runs S C t1 t2o t3o : result :=
  'let finally := fun S1 R =>
    match t3o with
    | None => res_ter S1 R
    | Some t3 =>
      if_success (runs_type_stat runs S1 C t3) (fun S2 rv' =>
        res_ter S2 R)
    end
    in
  if_any_or_throw (runs_type_stat runs S C t1) finally (fun S1 v =>
    match t2o with
    | None => finally S1 (res_throw v)
    | Some (x, t2) =>
      'let lex := execution_ctx_lexical_env C in
      'let p := lexical_env_alloc_decl S1 lex in (* LATER: ['let] on pair *)
      let '(lex', S') := p in
      match lex' with
      | L :: oldlex =>
        if_void (env_record_create_set_mutable_binding
          runs S' C L x None v throw_irrelevant) (fun S2 =>
            let C' := execution_ctx_with_lex C lex' in
            if_ter (runs_type_stat runs S2 C' t2) finally)
      | nil =>
        impossible_with_heap_because S' "Empty lexical environnment in [run_stat_try]."
      end
    end).

Definition run_stat_throw runs S C e : result :=
  if_spec (run_expr_get_value runs S C e) (fun S1 v1 =>
    res_ter S1 (res_throw v1)).

Definition run_stat_return runs S C eo : result :=
  match eo with
  | None =>
    out_ter S (res_return undef)
  | Some e =>
    if_spec (run_expr_get_value runs S C e) (fun S1 v1 =>
      res_ter S1 (res_return v1))
  end.

Definition run_stat_for_loop runs S C labs rv eo2 eo3 t : result :=
  (* Corresponds to the extended term [stat_for_2] in the rules. *)
  'let follows := fun S =>
    if_ter (runs_type_stat runs S C t) (fun S R =>
      'let rv' := ifb res_value R <> resvalue_empty then res_value R else rv in
      'let loop := fun S => runs_type_stat_for_loop runs S C labs rv' eo2 eo3 t in
      ifb res_type R = restype_break /\ res_label_in R labs then
        res_ter S rv'
      else (
        ifb res_type R = restype_normal
          \/ (res_type R = restype_continue /\ res_label_in R labs)
        then
          match eo3 with
          | None => loop S
          | Some e3 =>
              if_spec (run_expr_get_value runs S C e3) (fun S v3 =>
                loop S)
          end
        else res_ter S R
      ))
  in match eo2 with
  | None => follows S
  | Some e2 =>
    if_spec (run_expr_get_value runs S C e2) (fun S v2 =>
      'let b := convert_value_to_boolean v2 in
      if b then follows S
      else res_ter S rv)
  end.

Definition run_stat_for runs S C labs eo1 eo2 eo3 t : result :=
  let follows S :=
    runs_type_stat_for_loop runs S C labs resvalue_empty eo2 eo3 t
  in match eo1 with
  | None => follows S
  | Some e1 =>
    if_spec (run_expr_get_value runs S C e1) (fun S v1 =>
      follows S)
  end.

Definition run_stat_for_var runs S C labs ds eo2 eo3 t : result :=
  if_ter (runs_type_stat runs S C (stat_var_decl ds)) (fun S R =>
    runs_type_stat_for_loop runs S C labs resvalue_empty eo2 eo3 t).


(**************************************************************)
(** ** Definition of the interpreter *)

Definition run_expr runs S C e : result :=
  match e with

  | expr_literal i =>
    out_ter S (convert_literal_to_prim i)

  | expr_identifier x =>
    if_spec (identifier_resolution runs S C x) res_ter

  | expr_unary_op op e =>
    run_unary_op runs S C op e

  | expr_binary_op e1 op e2 =>
    run_expr_binary_op runs S C op e1 e2

  | expr_object pds =>
    if_object (run_construct_prealloc runs S C prealloc_object nil) (fun S1 l =>
      init_object runs S1 C l pds)

  | expr_member e1 f =>
    runs_type_expr runs S C (expr_access e1 (expr_literal (literal_string f)))

  | expr_access e1 e2 =>
    run_expr_access runs S C e1 e2

  | expr_assign e1 opo e2 =>
    run_expr_assign runs S C opo e1 e2

  | expr_function fo args bd =>
    run_expr_function runs S C fo args bd

  | expr_call e1 e2s =>
    run_expr_call runs S C e1 e2s

  | expr_this =>
    out_ter S (execution_ctx_this_binding C)

  | expr_new e1 e2s =>
    run_expr_new runs S C e1 e2s

  | expr_conditional e1 e2 e3 =>
    run_expr_conditionnal runs S C e1 e2 e3

  end.

(**************************************************************)

Definition run_stat runs S C t : result :=
  match t with

  | stat_expr e =>
    if_spec (run_expr_get_value runs S C e) res_ter

  | stat_var_decl xeos =>
    run_var_decl runs S C xeos

  | stat_block ts =>
    run_block runs S C (LibList.rev ts)

  | stat_label lab t =>
    run_stat_label runs S C lab t

  | stat_with e1 t2 =>
    run_stat_with runs S C e1 t2

  | stat_if e1 t2 to =>
    run_stat_if runs S C e1 t2 to

  | stat_do_while ls t1 e2 =>
    runs_type_stat_do_while runs S C resvalue_empty ls e2 t1

  | stat_while ls e1 t2 =>
    runs_type_stat_while runs S C resvalue_empty ls e1 t2

  | stat_throw e =>
    run_stat_throw runs S C e

  | stat_try t1 t2o t3o =>
    run_stat_try runs S C t1 t2o t3o

  | stat_return eo =>
    run_stat_return runs S C eo

  | stat_break so =>
    out_ter S (res_break so)

  | stat_continue so =>
    out_ter S (res_continue so)

  | stat_for ls eo1 eo2 eo3 s =>
    run_stat_for runs S C ls eo1 eo2 eo3 s

  | stat_for_var ls ds eo2 eo3 s =>
    run_stat_for_var runs S C ls ds eo2 eo3 s

  | stat_for_in ls e1 e2 s =>
    result_not_yet_implemented (* LATER *)

  | stat_for_in_var ls x e1o e2 s =>
    result_not_yet_implemented (* LATER *)

  | stat_debugger =>
    out_ter S res_empty

  | stat_switch labs e sb =>
    run_stat_switch runs S C labs e sb

  end.

(**************************************************************)

Fixpoint run_elements runs S C (els_rev : elements) : result :=
  match els_rev with
  | nil =>
    out_ter S resvalue_empty
  | el :: els_rev' =>
    if_success (run_elements runs S C els_rev') (fun S0 rv0 =>
      match el with
      | element_stat t =>
        if_ter (runs_type_stat runs S0 C t) (fun S1 R1 =>
          let R2 := res_overwrite_value_if_empty rv0 R1 in
          res_out (out_ter S1 R2))
      | element_func_decl name args bd => res_ter S0 rv0
      end)
  end.

(**************************************************************)

Definition run_prog runs S C p : result :=
  match p with

  | prog_intro str els =>
    run_elements runs S C (LibList.rev els)

  end.

(**************************************************************)

Fixpoint push runs S C l args ilen: result :=
  (* Corresponds to the construction [spec_call_array_proto_push_3] of the specification. *)
  'let vlen := JsNumber.of_int ilen
  in match args with
  | nil =>
    if_not_throw (object_put runs S C l "length" vlen throw_true) (fun S _ =>
      out_ter S vlen)
  | v::vs =>
    if_string (to_string runs S C vlen) (fun S slen =>
      if_not_throw (object_put runs S C l slen v throw_true) (fun S _ =>
        push runs S C l vs (ilen + 1)))
  end.

Definition run_call_prealloc runs S C B vthis (args : list value) : result :=
  match B with

  | prealloc_global_is_nan =>
    let v := get_arg 0 args in
    if_number (to_number runs S C v) (fun S0 n =>
      res_ter S0 (decide (n = JsNumber.nan)))

  | prealloc_global_is_finite =>
    let v := get_arg 0 args in
    if_number (to_number runs S C v) (fun S0 n =>
      res_ter S0 (neg
        (decide (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity))))

  | prealloc_object_get_proto_of =>
    match get_arg 0 args with
    | value_object l =>
      if_some (run_object_method object_proto_ S l) (fun proto =>
        res_ter S proto)
    | value_prim _ =>
      run_error S native_error_type
    end

  | prealloc_object_get_own_prop_descriptor =>
    match get_arg 0 args with
    | value_object l =>
      if_string (to_string runs S C (get_arg 1 args)) (fun S1 x =>
      if_spec (runs_type_object_get_own_prop runs S1 C l x) (fun S2 D =>
      from_prop_descriptor runs S2 C D))
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_seal =>
    match get_arg 0 args with
    | value_object l =>
      if_some (pick_option (object_properties_keys_as_list S l)) (
        (fix object_seal S0 xs : result :=
          match xs with
          | nil =>
            if_some (run_object_heap_set_extensible false S0 l) (fun S1 =>
              res_ter S1 l)
          | x :: xs' =>
            if_spec (runs_type_object_get_own_prop runs S0 C l x) (fun S1 D =>
              match D with
              | full_descriptor_some A =>
                let A' :=
                  if attributes_configurable A then
                    let Desc :=
                      descriptor_intro None None None None None (Some false)
                    in attributes_update A Desc
                  else A
                in if_bool (object_define_own_prop runs S1 C l x A' true) (fun S2 _ =>
                  object_seal S2 xs')
              | full_descriptor_undef =>
                impossible_with_heap_because S1 "[run_call_prealloc], [object_seal] case:  Undefined descriptor found in a place where it shouldn't."
              end)
          end) S)
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_is_sealed =>
    let v := get_arg 0 args in
    match v with
    | value_object l =>
      if_some (pick_option (object_properties_keys_as_list S l))
        (fix object_is_sealed xs : result :=
          match xs with
          | nil =>
            if_some (run_object_method object_extensible_ S l) (fun ext =>
              res_ter S (neg ext))
          | x :: xs' =>
            if_spec (runs_type_object_get_own_prop runs S C l x) (fun S0 D =>
              match D with
              | full_descriptor_some A =>
                if attributes_configurable A then
                  res_ter S false
                else object_is_sealed xs'
              | full_descriptor_undef =>
                impossible_with_heap_because S0 "[run_call_prealloc], [object_is_sealed] case:  Undefined descriptor found in a place where it shouldn't."
              end)
          end)
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_freeze =>
    let v := get_arg 0 args in
    match v with
    | value_object l =>
      if_some (pick_option (object_properties_keys_as_list S l)) (
        (fix object_freeze S0 xs : result :=
          match xs with
          | nil =>
            if_some (run_object_heap_set_extensible false S0 l) (fun S1 =>
              res_ter S1 l)
          | x :: xs' =>
            if_spec (runs_type_object_get_own_prop runs S0 C l x) (fun S1 D =>
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
                in if_bool (object_define_own_prop runs S1 C l x A'' true) (fun S2 _ =>
                  object_freeze S2 xs')
              | full_descriptor_undef =>
                impossible_with_heap_because S1 "[run_call], [object_freeze] case:  Undefined descriptor found in a place where it shouldn't."
              end)
          end) S)
    | value_prim _ => run_error S native_error_type
    end


  | prealloc_object_is_frozen =>
    let v := get_arg 0 args in
    match v with
    | value_object l =>
      if_some (pick_option (object_properties_keys_as_list S l))
        (fix object_is_frozen xs : result :=
          match xs with
          | nil =>
            if_some (run_object_method object_extensible_ S l) (fun ext =>
              res_ter S (neg ext))
          | x :: xs' =>
            if_spec (runs_type_object_get_own_prop runs S C l x) (fun S0 D =>
              'let check_configurable := fun A =>
                if attributes_configurable A then
                  res_ter S0 false
                else object_is_frozen xs'
              in match D with
              | attributes_data_of Ad =>
                if attributes_writable Ad then
                  res_ter S0 false
                else check_configurable Ad
              | attributes_accessor_of Aa =>
                check_configurable Aa
              | full_descriptor_undef =>
                impossible_with_heap_because S0 "[run_call_prealloc], [object_is_frozen] case:  Undefined descriptor found in a place where it shouldn't."
              end)
          end)
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_is_extensible =>
    let v := get_arg 0 args in
    match v with
    | value_object l =>
      if_some (run_object_method object_extensible_ S l) (res_ter S)
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_prevent_extensions =>
    let v := get_arg 0 args in
    match v with
    | value_object l =>
      if_some (pick_option (object_binds S l)) (fun O =>
        let O1 := object_with_extension O false in
        let S' := object_write S l O1 in
        res_ter S' l)
    | value_prim _ => run_error S native_error_type
    end

  | prealloc_object_proto_to_string =>
    match vthis with
    | undef => out_ter S "[object Undefined]"
    | null => out_ter S "[object Null]"
    | _ =>
      if_object (to_object S vthis) (fun S1 l =>
        if_some (run_object_method object_class_ S1 l) (fun s =>
          res_ter S1 ("[object " ++ s ++ "]")))
    end

  | prealloc_object_proto_value_of =>
    to_object S vthis

  | prealloc_object_proto_is_prototype_of =>
    let v := get_arg 0 args in
    match v with
    | value_prim _ =>
      out_ter S false
    | value_object l =>
      if_object (to_object S vthis) (fun S1 lo =>
        runs_type_object_proto_is_prototype_of runs S1 lo l)
    end

  | prealloc_object_proto_prop_is_enumerable =>
    let v := get_arg 0 args in
    if_string (to_string runs S C v) (fun S1 x =>
      if_object (to_object S1 vthis) (fun S2 l =>
        if_spec (runs_type_object_get_own_prop runs S2 C l x) (fun S3 D =>
          match D with
          | full_descriptor_undef =>
            res_ter S3 false
          | full_descriptor_some A =>
            res_ter S3 (attributes_enumerable A)
          end)))

  | prealloc_object_proto_has_own_prop =>
    let v := get_arg 0 args in
    if_string (to_string runs S C v) (fun S1 x =>
      if_object (to_object S1 vthis) (fun S2 l =>
        if_spec (runs_type_object_get_own_prop runs S2 C l x) (fun S3 D =>
          match D with
          | full_descriptor_undef =>
            res_ter S3 false
          | _ => res_ter S3 true
          end)))

  | prealloc_function_proto =>
    out_ter S undef

  | prealloc_string_proto_to_string
  | prealloc_string_proto_value_of =>
    match vthis with
    | value_prim p =>
      ifb type_of vthis = type_string
      then res_ter S vthis
      else run_error S native_error_type
    | value_object l =>
      if_some (run_object_method object_class_ S l) (fun s =>
        ifb s = "String"
        then run_object_prim_value S l
        else run_error S native_error_type)
    end

  | prealloc_bool =>
    let v := get_arg 0 args in
    out_ter S (convert_value_to_boolean v)

  | prealloc_bool_proto_to_string =>
    if_bool (bool_proto_value_of_call S vthis) (fun S' b =>
      res_ter S' (convert_bool_to_string b))

  | prealloc_bool_proto_value_of =>
    bool_proto_value_of_call S vthis

  | prealloc_number =>
    ifb args = nil then
      out_ter S JsNumber.zero
    else
      let v := get_arg 0 args in
      to_number runs S C v

  | prealloc_number_proto_value_of =>
    if_some (run_value_viewable_as_prim "Number" S vthis) (fun vw =>
      match vw with
      | Some (prim_number n) => res_ter S n
      | _ => run_error S native_error_type
      end)

  | prealloc_error =>
    'let v := get_arg 0 args in
    build_error S prealloc_error_proto v

  | prealloc_native_error_proto ne =>
    'let v := get_arg 0 args in
    build_error S B v

  | prealloc_throw_type_error =>
    run_error S native_error_type

  | prealloc_array_proto_pop =>
    if_object (to_object S vthis) (fun S l =>
      if_value (run_object_get runs S C l "length") (fun S vlen =>
        if_spec (to_uint32 runs S C vlen) (fun S ilen =>
          ifb decide (ilen = 0) then
            if_not_throw (object_put runs S C l "length" JsNumber.zero throw_true) (fun S _ =>
              out_ter S undef)
          else
            if_string (to_string runs S C (JsNumber.of_int (ilen - 1))) (fun S sindx =>
              if_value (run_object_get runs S C l sindx) (fun S velem =>
                if_not_throw (object_delete_default runs S C l sindx throw_true) (fun S _ =>
                  if_not_throw (object_put runs S C l "length" sindx throw_true) (fun S _ =>
                    out_ter S velem)))))))

  | prealloc_array_proto_push =>
    if_object (to_object S vthis) (fun S l =>
      if_value (run_object_get runs S C l "length") (fun S vlen =>
        if_spec (to_uint32 runs S C vlen) (fun S ilen =>
          push runs S C l args ilen)))

  | _ =>
    result_not_yet_implemented (* LATER *)

  end.

(**************************************************************)

Definition run_call runs S C l vthis args : result :=
  if_some (run_object_method object_call_ S l) (fun co =>
    if_some co (fun c =>
      match c with
      | call_default =>
        entering_func_code runs S C l vthis args
      | call_prealloc B =>
        run_call_prealloc runs S C B vthis args
      | call_after_bind =>
        impossible_with_heap_because S "[run_call_full]:  [call_after_bind] found."
      end)).

(**************************************************************)

Definition run_javascript runs p : result :=
  let S := state_initial in
  let p' := add_infos_prog strictness_false p in
  let C := execution_ctx_initial (prog_intro_strictness p') in
  if_void (execution_ctx_binding_inst runs S C codetype_global None p' nil) (fun S' =>
    runs_type_prog runs S' C p').


(**************************************************************)
(** ** Closing the Loops *)

Fixpoint runs max_step : runs_type :=
  match max_step with
  | O => {|
      runs_type_expr := fun S _ _ => result_bottom S;
      runs_type_stat := fun S _ _ => result_bottom S;
      runs_type_prog := fun S _ _ => result_bottom S;
      runs_type_call := fun S _ _ _ _ => result_bottom S;
      runs_type_function_has_instance := fun S _ _ => result_bottom S;
      runs_type_stat_while := fun S _ _ _ _ _ => result_bottom S;
      runs_type_stat_do_while := fun S _ _ _ _ _ => result_bottom S;
      runs_type_stat_for_loop := fun S _ _ _ _ _ _ => result_bottom S;
      runs_type_object_delete := fun S _ _ _ _ => result_bottom S;
      runs_type_object_get_own_prop := fun S _ _ _ => result_bottom S;
      runs_type_object_get_prop := fun S _ _ _ => result_bottom S;
      runs_type_object_get := fun S _ _ _ => result_bottom S;
      runs_type_object_proto_is_prototype_of := fun S _ _ => result_bottom S;
      runs_type_object_put := fun S _ _ _ _ _ => result_bottom S;
      runs_type_equal := fun S _ _ _ => result_bottom S;
      runs_type_to_integer := fun S _ _ => result_bottom S;
      runs_type_to_string := fun S _ _ => result_bottom S
    |}
  | S max_step' =>
    let wrap {A : Type} (f : runs_type -> state -> A) S : A :=
      let runs' := runs max_step' in
      f runs' S
    in {|
      runs_type_expr := wrap run_expr;
      runs_type_stat := wrap run_stat;
      runs_type_prog := wrap run_prog;
      runs_type_call := wrap run_call;
      runs_type_function_has_instance :=
        wrap run_function_has_instance;
      runs_type_stat_while := wrap run_stat_while;
      runs_type_stat_do_while := wrap run_stat_do_while;
      runs_type_stat_for_loop := wrap run_stat_for_loop;
      runs_type_object_delete := wrap object_delete;
      runs_type_object_get_own_prop :=
        wrap run_object_get_own_prop;
      runs_type_object_get_prop :=
        wrap run_object_get_prop;
      runs_type_object_get :=
        wrap run_object_get;
      runs_type_object_proto_is_prototype_of :=
        wrap object_proto_is_prototype_of;
      runs_type_object_put := wrap object_put;
      runs_type_equal := wrap run_equal;
      runs_type_to_integer := wrap to_integer;
      runs_type_to_string := wrap to_string
    |}
  end.

End Interpreter.

