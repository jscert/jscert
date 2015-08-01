Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsSyntaxInfos JsCommon JsCommonAux JsPreliminary JsInit.

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

(*
  * Definitions of the datatypes used.
  * Monadic constructors.
*)


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

Definition not_yet_implemented_because {T} s : resultof T := result_not_yet_implemented.

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

Definition get_arg_first_and_rest (lv : list value) :=
 (get_arg 0 lv, match lv with
                 | nil => nil
                 | _ :: rest => rest
                end).        

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


