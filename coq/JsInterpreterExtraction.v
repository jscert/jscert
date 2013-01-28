Set Implicit Arguments.
Require Import JsSyntax JsInterpreter JsInit.
Require Import LibFix LibList.

Require Export Shared.
Require Export Ascii String.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc LibHeap.
Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.



(**************************************************************)
(** ** Numerical values *)

(* TODO: remove duplication with JsNumber *)

Definition number_of_int : int -> number :=
  Fappli_IEEE_bits.b64_of_bits.

Definition number_add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition number_mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition number_div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.

(* Here stands some commands to extract relatively correctly the interpreter to Ocaml. *)
Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(* number *)
Require Import ExtrOcamlZInt.
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> let f = ldexp (float_of_int m) e in if s then f else -.f)"
].
Extract Constant number_of_int => float_of_int.
(* Optimal fixpoint. *)
Extraction Inline FixFun3 FixFun3Mod FixFun4 FixFun4Mod FixFunMod curry3 uncurry3 curry4 uncurry4.
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline epsilon epsilon_def classicT arbitrary indefinite_description Inhab_witness Fix isTrue.

(* number *)
Require Import ExtrOcamlZInt.
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> let f = ldexp (float_of_int m) e in if s then f else -.f)"
].

Extract Constant number_of_int => float_of_int.
Extract Constant JsNumber_to_int => "(int_of_float)".

Extract Constant JsNumber.nan => "nan".
Extract Constant JsNumber.zero => "0.".
Extract Constant JsNumber.neg_zero => "(-0.)".
Extract Constant JsNumber.one => "1.".
Extract Constant JsNumber.infinity => "infinity".
Extract Constant JsNumber.neg_infinity => "(-.infinity)".
Extract Constant JsNumber.floor => "floor".
Extract Constant JsNumber.absolute => "abs_float".
Extract Constant JsNumber.from_string => "(fun s -> float_of_string (String.concat """" (List.map (String.make 1) s)))".
Extract Constant JsNumber.to_string =>
  "(fun f -> let ret = ref [] in (* Ugly, but the API for Ocaml string is not very functionnal... *)
    String.iter (fun c -> ret := c :: !ret) (string_of_float f);
    List.rev !ret)".
Extract Constant JsNumber.add => "(+.)".
Extract Constant JsNumber.sub => "(-.)".
Extract Constant JsNumber.mult => "( *. )".
Extract Constant JsNumber.div => "(/.)".
Extract Constant JsNumber.fmod => "mod_float".
Extract Constant JsNumber.neg => "(~-.)".
Extract Constant JsNumber.sign => "(fun f -> float_of_int (compare f 0.))".
Extract Constant JsNumber.number_comparable => "(fun n1 n2 -> 0 = compare n1 n2)".
Extract Constant JsNumber.lt_bool => "(<)".

Extract Constant int_of_char => "int_of_char".

Extract Constant builtin_compare => "(=)".
Extract Constant ascii_compare => "(=)".
Extract Constant le_int_decidable => "(<=)".
Extract Constant int_lt_dec => "(<)".

Extract Constant env_loc_global_env_record => "0".

(* The following functions make pattern matches with floats and shall thus be removed. *)
Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

(* New options for the interpreter to work in Coq 8.4 *)
Set Extraction AccessOpaque.
Extract Constant Pos.succ => "Pervasives.succ". (* Martin:  Because of a bug of the extraction printer, we are forced to precise the way we want such objects to be extracted... *)

(* These parameters are implementation-dependant according to the spec.
   I've chosed some very simple values, but we could choose another thing for them. *)
Extract Constant object_builtin_global_proto => "(Value_prim Prim_null)".
Extract Constant object_builtin_global_class => "(
  let rec aux s = function
  | 0 -> []
  | n -> let n' = n - 1 in
    s.[n'] :: aux s n'
  in let aux2 s =
    List.rev (aux s (String.length s))
  in aux2 ""GlobalClass"")".

Extraction "interp/src/interpreter.ml" state_initial execution_ctx_initial run_prog.



(* -- LATER: extract inequality_test_string in more efficient way*)

