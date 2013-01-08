Set Implicit Arguments.
Require Import JsSyntax JsInterpreter JsSemanticsInit.
Require Import LibFix LibList.


Require Export Shared.
Require Export Ascii String.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc LibHeap.
Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.


(**************************************************************)
(** ** To be moved on JsSemanticsInit *)

Definition execution_ctx_initial :=
  {| execution_ctx_lexical_env := lexical_env_initial;
     execution_ctx_variable_env := nil;
     execution_ctx_this_binding := builtin_object;
     execution_ctx_strict := false |}.

(**************************************************************)
(** ** Numerical values *)

Definition number_of_int : int -> number := 
  Fappli_IEEE_bits.b64_of_bits.

Definition number_add : number -> number -> number :=
  Fappli_IEEE_bits.b64_plus Fappli_IEEE.mode_NE.

Definition number_mult : number -> number -> number :=
  Fappli_IEEE_bits.b64_mult Fappli_IEEE.mode_NE.

Definition number_div : number -> number -> number :=
  Fappli_IEEE_bits.b64_div Fappli_IEEE.mode_NE.


Section Example.

(* To have something readable. *)
Definition expr_int i := expr_literal (literal_number (number_of_int i)).

(* Waiting for a special undefined location. -- Martin *)
Definition expr_undef := expr_unary_op unary_op_void (expr_int 42).


Definition seq (l : list stat) :=
  match fold_right
      (fun s acc =>
        match acc with
        | None => Some s
        | Some s' => Some (stat_seq s s')
        end)
      None l
  with
  | None => expr_undef
  | Some s => s
  end.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Parameter max_int : nat.

(* (* ------ prog1.js ------ *)
convert = function(n) { return n (function(n) { return n + 1 }) (0) };

succ = function(n) { return function(f) { return function(x) {
    return n (f) (f (x))
  }}};

zero = function(f) { return function(x) { return x } };

plus = function(x) { return function(y) { return x (succ) (y) }};

times = function(x) { return function(y) { return x (plus (y)) (zero) }};

exp = function(x) { return function(y) { return y (x) }};

var one = succ (zero);
var two = plus (one) (one);
var three = plus (two) (one);

var six = times (three) (two);

convert (exp (two) (six))
*)

Definition prog1 :=
  seq [
    stat_expr (expr_assign (expr_variable "convert") None (expr_function None ["n"%string] (
      expr_call (expr_call (expr_variable "n") [expr_function None ["n"%string] (
        expr_binary_op (expr_variable "n") binary_op_add (
          expr_int 1)
        )]) [expr_int 0]
    ))) ;
    stat_expr (expr_assign (expr_variable "succ") None (expr_function None ["n"%string] (expr_function None ["f"%string] (expr_function None ["x"%string] (
      expr_call (expr_call (expr_variable "n") [expr_variable "f"])
        [expr_call (expr_variable "f") [expr_variable "x"]]
    ))))) ;
    stat_expr (expr_assign (expr_variable "zero") None (expr_function None ["f"%string] (expr_function None ["x"%string] (expr_variable "x")))) ;
    stat_expr (expr_assign (expr_variable "plus") None (expr_function None ["x"%string] (expr_function None  ["y"%string] (
      expr_call (expr_call (expr_variable "x") [expr_variable "succ"]) [expr_variable "y"])))) ;
    stat_expr (expr_assign (expr_variable "times") None (expr_function None ["x"%string] (expr_function None  ["y"%string] (
      expr_call (expr_call (expr_variable "x") [expr_call (expr_variable "plus") [expr_variable "y"]]) [expr_variable "zero"])))) ;
    stat_expr (expr_assign (expr_variable "exp") None (expr_function None ["x"%string] (expr_function None  ["y"%string] (
      expr_call (expr_variable "y") [expr_variable "x"])))) ;
    stat_var_decl "one"
      (Some (expr_call (expr_variable "succ") [expr_variable "zero"])) ;
    stat_var_decl "two"
      (Some (expr_call (expr_call (expr_variable "plus") [expr_variable "one"]) [expr_variable "one"])) ;
    stat_var_decl "three"
      (Some (expr_call (expr_call (expr_variable "plus") [expr_variable "two"]) [expr_variable "one"])) ;
    stat_var_decl "six"
      (Some (expr_call (expr_call (expr_variable "times") [expr_variable "three"]) [expr_variable "two"])) ;
    stat_expr (expr_call (expr_variable "convert")
      [expr_call (expr_call (expr_variable "exp") [expr_variable "two"]) [expr_variable "six"]])
  ].

Definition computation1 := run_prog max_int state_initial execution_ctx_initial prog1.

(* (* ------ prog2.js ------ *)
var id = function(x) { return x }; (* To deference the final value. *)

var f = function() {
  this.x = 0;
  this.g = function() { this.x = 1; return this };
  void 0 
  };

var h = function() { };
h.prototype = new f();

var test = new h();

id(test.g().x)
*)

Definition stat_var_decl' s e := 
  stat_var_decl s (Some e).
Definition expr_assign' e1 e2 :=
  expr_assign e1 None e2.

Definition prog2 := seq [
  stat_var_decl' "id" (expr_function None ["x"%string] (expr_variable "x")) ;
  stat_var_decl' "f" (expr_function None [] (
    seq [
      stat_expr (expr_assign' (expr_member expr_this "x") (expr_int 0)) ;
      stat_expr (expr_assign' (expr_member expr_this "g") (expr_function None [] (
        seq [
          stat_expr (expr_assign' (expr_member expr_this "x") (expr_int 1)) ;
          stat_expr expr_this
        ]
      ))) ;
      stat_expr expr_undef ]
    )) ;
  stat_var_decl' "h" (expr_function None [] (seq [])) ;
  stat_expr (expr_assign' (expr_member (expr_variable "h") "prototype") (
    expr_new (expr_variable "f") [])) ;
  stat_var_decl' "test" (expr_new (expr_variable "h") []) ;

  stat_expr (expr_call (expr_variable "id") [
    expr_member (expr_call (expr_member (expr_variable "test") "g") [])
      "x"])
  ].

Definition computation2 := run_prog max_int state_initial execution_ctx_initial prog2.

(* (* ------ prog3.js ------ *)
Object.prototype.x = 42;
var x = 24;
var f = function (){ return x; };
f()
*)

Definition prog3 := seq [
  (* expr_assign (expr_member (expr_member (expr_literal (value_loc loc_global)) "prototype") "x") (expr_int 24);*) (* This is not correct and the initial heap had to be modified to be able to use this example. *)
  stat_var_decl' "x" (expr_int 24) ;
  stat_var_decl' "f" (expr_function None [] (expr_variable "x")) ;
  stat_expr (expr_call (expr_variable "f") [])
  ].

Definition computation3 := run_prog max_int state_initial (* Old value:
    write init_heap loc_obj_proto (field_normal "x") (value_number (number_of_int 42))*)
  execution_ctx_initial prog3.

End Example.

(* Here stands some commands to extract relatively correctly the interpreter to Ocaml. *)
Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

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
Extract Constant number_add => "(+.)".
Extract Constant number_mult => "( *. )".
Extract Constant number_div => "(/.)".
Extract Constant number_of_int => float_of_int.
Extract Constant JsNumber.nan => "nan".
Extract Constant JsNumber.zero => "0.".
Extract Constant JsNumber.neg_zero => "(-0.)".
Extract Constant JsNumber.one => "1.".
Extract Constant JsNumber.infinity => "infinity".
Extract Constant JsNumber.neg_infinity => "(-infinity)".
Extract Constant JsNumber.floor => "floor".
Extract Constant JsNumber.absolute => "abs_float".
Extract Constant JsNumber.from_string => "(fun s -> float_of_string (String.concat """" (List.map (String.make 1) s)))".
Extract Constant JsNumber.to_string =>
  "(fun f -> let ret = ref [] in (* Ugly, but the API for Ocaml string is not ver functionnal... *)
    String.iter (fun c -> ret := c :: !ret) (string_of_float f);
    List.rev !ret)".
Extract Constant JsNumber.sign => "(fun f -> string_of_int (compare f 0.))".
Extract Constant JsNumber.mult => "( *. )".
Extract Constant JsNumber.number_comparable => "(=)".
Extract Constant JsNumber_to_int => "(float_of_int)".
(* The following functions make pattern matches with floats and shall thus be removed. *)
Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

(* New options for the interpreter to work in Coq 8.4 *)
Set Extraction AccessOpaque.
Extract Constant Pos.succ => "Pervasives.succ". (* Martin:  Because of a bug of the extraction printer, we are forced to precise the way we want such objects to be extracted... *)

(* Some constants *)
Extract Constant max_int => max_int.

Extraction "interp/src/interpreter.ml" computation1 computation2 computation3.

