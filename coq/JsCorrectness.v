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
(** Correctness Properties *)

Definition follow_spec {T Te : Type}
    (conv : T -> Te) (red : state -> execution_ctx -> Te -> out -> Prop)
    (run : state -> execution_ctx -> T -> result) := forall S C (e : T) S' res,
  run S C e = out_ter S' res ->
  red S C (conv e) (out_ter S' res).

Definition follow_expr := follow_spec expr_basic red_expr.
Definition follow_stat := follow_spec stat_basic red_stat.
Definition follow_prog := follow_spec prog_basic red_prog.
Definition follow_elements rv :=
  follow_spec (prog_1 rv) red_prog.
Definition follow_call vs :=
  follow_spec
    (fun B => spec_call_prealloc B vs)
    red_expr.
Definition follow_call_full l vs :=
  follow_spec
    (fun v => spec_call l v vs)
    red_expr.


Record runs_type_correct runs run_elements :=
  make_runs_type_correct {
    runs_type_correct_expr : follow_expr (runs_type_expr runs);
    runs_type_correct_stat : follow_stat (runs_type_stat runs);
    runs_type_correct_prog : follow_prog (runs_type_prog runs);
    runs_type_correct_elements : forall rv,
      follow_elements rv (fun S C => run_elements S C rv);
    runs_type_correct_call : forall vs,
      follow_call vs (fun S C B => runs_type_call runs S C B vs);
    runs_type_correct_call_full : forall l vs,
      follow_call_full l vs (fun S C vthis => runs_type_call_full runs S C l vthis vs)
  }.



(**************************************************************)
(** Monadic constructors *)

(* Unfolds one monadic contructor in the environnement, calling the
  continuation when getting an unsolved non-terminating reduction. *)
Ltac if_unmonad k :=
  match goal with

  | I: out_ter ?S1 ?R1 = out_ter ?S0 ?R0 |- ?g =>
    inverts~ I

  | I : if_ter ?o ?K = ?o0 |- ?g =>
    unfold if_ter in I;
    let o' := fresh "o" in
    let o'' := fresh "o" in
    let Eqo' := fresh "Eq" o' in
    sets_eq <- o' Eqo': o;
    destruct o' as [o''| |]; cbv beta in I;
      [destruct o'';
        [k I|]
      | k I | k I]

  | I : if_success_state ?rv ?o ?K = ?o0 |- ?g =>
    unfold if_success_state in I;
    if_unmonad k;
    match goal with
    | I : match res_type ?r with
          | restype_normal => ?C1
          | restype_break => ?C2
          | restype_continue => ?C3
          | restype_return => ?C4
          | restype_throw => ?C5
          end = _ |- _ =>
      tests: (abort r)
    | _ => idtac
    end

  end.

(**************************************************************)
(** Operations on objects *)

(* TODO
Lemma run_object_method_correct :
  forall Proj S l,
  (* TODO:  Add correctness properties. *)
    object_method Proj S l (run_object_method Proj S l).
Proof.
  introv. eexists. splits*.
  apply pick_spec.
  skip. (* Need properties about [l]. *)
Qed.
*)


(**************************************************************)
(** Operations on environments *)


(**************************************************************)
(** ** Main theorems *)

Theorem runs_correct : forall num,
  runs_type_correct (runs num) (run_elements num).
Proof.

  induction num.
   constructors; introv R; inverts R.

   lets [IHe IHs IHp IHel IHc IHcf]: (rm IHnum).
   constructors.

   (* run_expr *)
   skip.

   (* run_stat *)
   skip.

   (* run_prog *)
   intros S C p S' res R. destruct p as [str es]. simpls.
   forwards RC: IHel R. apply~ red_prog_prog.

   (* run_elements *)
   intros rv S C es S' res R. destruct es; simpls.
    inverts R. apply~ red_prog_1_nil.
    destruct e.
     if_unmonad ltac:(fun I => try inverts I).
    match goal with
    | I : match res_type ?r with
          | restype_normal => ?C1
          | restype_break => ?C2
          | restype_continue => ?C3
          | restype_return => ?C4
          | restype_throw => ?C5
          end = _,
      I' : _ = result_normal (out_ter ?s ?r) |- _ =>
      tests: (abort (out_ter s r)) end.

       destruct (res_type r). skip.
       inverts R. forwards RC: IHs Eqo.
         applys~ red_prog_1_cons_stat RC.
         apply~ red_prog_2. skip.
         apply red_prog_abort. reflexivity.
       skip.
     forwards RC: IHel R. apply~ red_prog_1_cons_funcdecl.

   (* run_call *)
   skip.

   (* run_call_full *)
   intros l vs S C v S' res R. simpls.
   skip.

Qed.

