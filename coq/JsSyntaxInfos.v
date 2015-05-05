Require Import JsSyntax JsSyntaxAux.


(**************************************************************)
(** ** Implicit Types *)

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.

Implicit Type fb : funcbody.
Implicit Type el : element.
Implicit Type str : strictness_flag.


(**************************************************************)
(** Annotate the AST of a program with label sets (used for
    break and continue), and propagate strictness information
    downwards in the AST (so that any function code under a
    strictness directive will be tagged as strict). Note 
    that label sets only accumulate at the head of loop 
    statements. *)

(** Propagate through expressions *)

Fixpoint add_infos_exp str e :=
   let f := add_infos_exp str in
   match e with
     | expr_this 
     | expr_identifier _
     | expr_literal _
     | expr_object _ => e

     (* _ARRAYS_ : Propagation into every element of the list *)
     | expr_array oes => expr_array (List.map (fun oe => match oe with
                                                          | None => None
                                                          | Some e => Some (f e)
                                                         end) oes)

     | expr_function so ss fb => expr_function so ss (add_infos_funcbody str fb)
     | expr_access e1 e2 => expr_access (f e1) (f e2)
     | expr_member e s => expr_member (f e) s
     | expr_new e es => expr_new (f e) (List.map f es)
     | expr_call e es => expr_call (f e) (List.map f es)
     | expr_unary_op op e => expr_unary_op op (f e)
     | expr_binary_op e1 op e2 => expr_binary_op (f e1) op (f e2)
     | expr_conditional e1 e2 e3 => expr_conditional (f e1) (f e2) (f e3)
     | expr_assign e1 op e2 => expr_assign (f e1) op (f e2)
   end
   
(** Propagate through function bodies *)

with add_infos_funcbody str fb :=
   match fb with
     | funcbody_intro p s => funcbody_intro (add_infos_prog str p) s
   end

(** Propagate through statements *)

with add_infos_stat str labs t :=
  let opt {A} (f : A -> A) (smth : option A) :=
    match smth with
      | Some smth => Some (f smth)
      | None => None
    end in
  let f := add_infos_stat str label_set_empty in
  let fo := opt f in
  let fe := add_infos_exp str in
  let feo := opt fe in
  let fsb := add_infos_switchbody str in
  match t with
    | stat_expr e => stat_expr (fe e)
    | stat_label l t => stat_label l (add_infos_stat str (label_set_add l labs) t)
    | stat_block ts => stat_block (List.map f ts)
    | stat_var_decl vars => stat_var_decl (List.map (fun var =>
        let '(s, eo) := var in (s, feo eo)) vars)
    | stat_if e t to => stat_if (fe e) (f t) (fo to) 
    | stat_do_while _ t e => stat_do_while (label_set_add_empty labs) (f t) (fe e)
    | stat_while _ e t => stat_while (label_set_add_empty labs) (fe e) (f t)
    | stat_with e t => stat_with (fe e) (f t)
    | stat_throw e => stat_throw (fe e)
    | stat_return eo => stat_return (feo eo)
    | stat_break lopt => stat_break lopt
    | stat_continue lopt => stat_continue lopt
    | stat_try t catch to =>
      stat_try (f t) (opt (fun c => let '(cs, t) := c in (cs, f t)) catch) (fo to) 
    | stat_for _ eo1 eo2 eo3 t =>
      stat_for (label_set_add_empty labs) (feo eo1) (feo eo2) (feo eo3) (f t)
    | stat_for_var _ vars eo2 eo3 t =>
      stat_for_var (label_set_add_empty labs) (List.map (fun var =>
        let '(s, eo) := var in (s, feo eo)) vars) (feo eo2) (feo eo3) (f t)
    | stat_for_in _ e1 e2 t =>
      stat_for_in (label_set_add_empty labs) (fe e1) (fe e2) (f t)
    | stat_for_in_var _ str eo e t =>
      stat_for_in_var (label_set_add_empty labs) str (feo eo) (fe e) (f t)
    | stat_debugger => stat_debugger
    | stat_switch labs e ts => stat_switch (label_set_add_empty labs) (fe e) (fsb ts) 
  end

(** Propagate through switch *)

with add_infos_switchbody str ts :=
  let fe := add_infos_exp str in
  let fs := add_infos_stat str label_set_empty in
  let f sc :=
    match sc with
    | switchclause_intro e l => switchclause_intro (fe e) (List.map fs l)
    end in
  match ts with
  | switchbody_nodefault l => switchbody_nodefault (List.map f l)
  | switchbody_withdefault l1 s l2 =>
    switchbody_withdefault (List.map f l1) (List.map fs s) (List.map f l2)
  end
(** Propagate through programs *)

with add_infos_prog str p :=
  match p with
    | prog_intro str' els =>  
      let str'' := (str || str') in
      prog_intro str'' (List.map (add_infos_element str'') els)
  end
 
(** Propagate through program elements *)

with add_infos_element str el :=
  match el with
    | element_stat t => element_stat (add_infos_stat str label_set_empty t)
    | element_func_decl s ss fb => element_func_decl s ss (add_infos_funcbody str fb)
  end.

