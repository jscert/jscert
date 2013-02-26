Set Implicit Arguments.
Require Import Shared.
Require Import LibFix LibList.
Require Import JsSyntax JsSyntaxAux JsPreliminary JsPreliminaryAux.
Require Import JsInterpreter JsPrettyInterm JsPrettyRules.


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
Implicit Type ct : codetype.

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
(** Generic constructions *)

Lemma get_arg_correct : forall args vs,
  arguments_from args vs ->
  forall num,
    num < length vs ->
    get_arg num args = LibList.nth num vs.
Proof.
  introv A. induction~ A.
   introv I. false I. lets (I'&_): (rm I). inverts~ I'.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_nil.
    rewrite length_cons in I. nat_math.
   introv I. destruct* num. simpl. rewrite <- IHA.
    unfolds. repeat rewrite~ get_nth_cons.
    rewrite length_cons in I. nat_math.
Qed.


(**************************************************************)
(** Monadic constructors *)

(* Small tests to automate the proof.
Lemma test : forall res S0 R0,
  if_ter res (fun S R =>
    result_stuck) = out_ter S0 R0.
Proof.
  introv.

  tests: (exists S R, res = out_ter S R).
   lets (S&R&E): (rm C). rewrite E in * |- *. clear E.
   simpl.

   skip.

  cuts: ((forall S R, ~ res = out_ter S R) ->
    res = out_ter S0 R0).
  (* TODO:  Add [lets] *)
  destruct res as [o|r1|r2]; [
    destruct o; [
      simpl; rewrite H; [
        reflexivity
        | introv; discriminate ]
      | false C; repeat eexists ]
    | auto*
    | auto* ].

  skip.
Qed.

Ltac unmonad_if_ter :=
  match goal with
  | 
  end. *)


(**************************************************************)
(** ** Main theorem *)

Theorem run_prog_correct : forall num S C p o,
  (* TODO:  Add correctness statements. *)
  run_prog num S C p = o ->
  red_prog S C p o

with run_stat_correct : forall num S C t o,
  run_stat num S C t = o ->
  red_stat S C t o

with run_expr_correct : forall num S C e o,
  run_expr num S C e = o ->
  red_expr S C e o.
Proof.
Admitted.


