Set Implicit Arguments.
Require Import JsSyntax.
Require Import LibFix LibList.


(** For extraction *)

Extraction Language Ocaml.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

(** Extraction for the different files *)

Extraction "syntax.ml" expr.

