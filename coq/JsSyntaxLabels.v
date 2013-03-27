Require Import JsSyntax.

(**************************************************************)
(** Annotating program with label sets *)

Fixpoint add_label_sets_to_exp (e : expr) : expr :=
   let f := add_label_sets_to_exp in
   match e with
     | expr_this 
     | expr_identifier _
     | expr_literal _
     | expr_object _ => e
     | expr_function so ss fb => expr_function so ss (add_label_sets_to_funcbody fb)
     | expr_access e1 e2 => expr_access (f e1) (f e2)
     | expr_member e s => expr_member (f e) s
     | expr_new e es => expr_new (f e) (List.map f es)
     | expr_call e es => expr_call (f e) (List.map f es)
     | expr_unary_op op e => expr_unary_op op (f e)
     | expr_binary_op e1 op e2 => expr_binary_op (f e1) op (f e2)
     | expr_conditional e1 e2 e3 => expr_conditional (f e1) (f e2) (f e3)
     | expr_assign e1 op e2 => expr_assign (f e1) op (f e2)
   end
   
with add_label_sets_to_funcbody (fb: funcbody) : funcbody :=
   match fb with
     | funcbody_intro p s => funcbody_intro (add_label_sets_to_prog p) s
   end
   
with add_label_sets_to_prog (p : prog) : prog :=
  match p with
    | prog_intro sf elems => prog_intro sf (List.map add_label_sets_to_element elems)
  end
 
with add_label_sets_to_element (elem : element) : element :=
  match elem with
    | element_stat t => element_stat (add_label_sets_to_stat \{} t)
    | element_func_decl s ss fb => element_func_decl s ss (add_label_sets_to_funcbody fb)
  end

with add_label_sets_to_stat (lset : label_set) (t: stat) : stat :=
  let opt {A} (f : A -> A ) (smth : option A) :=
    match smth with
      | Some smth => Some (f smth)
      | None => None
    end in
  let f := add_label_sets_to_stat \{} in
  let fo := opt f in
  let fe := add_label_sets_to_exp in
  let feo := opt fe in
  match t with 
    | stat_expr e => stat_expr (fe e)
    | stat_label l t => stat_label l (add_label_sets_to_stat (\{l} \u lset) t)
    | stat_block ts => stat_block (List.map f ts)
    | stat_var_decl vars => stat_var_decl (List.map (fun var =>
      match var with (s, eo) => (s, feo eo) end) vars)
    | stat_if e t to => stat_if (fe e) (f t) (fo to) 
    | stat_do_while _ t e => stat_do_while lset (f t) (fe e)
    | stat_while _ e t => stat_while lset (fe e) (f t)
    | stat_with e t => stat_with (fe e) (f t)
    | stat_throw e => stat_throw (fe e)
    | stat_return eo => stat_return (feo eo)
    | stat_break lopt => stat_break lopt
    | stat_continue lopt => stat_continue lopt
    | stat_try t catch to =>
      stat_try (f t) (opt (fun c => match c with (cs, t) => (cs, f t) end) catch) (fo to) 
    | stat_for_in _ e1 e2 t => stat_for_in lset (fe e1) (fe e2) (f t)
    | stat_for_in_var _ str eo e t => stat_for_in_var lset str (feo eo) (fe e) (f t)
    | stat_debugger => stat_debugger
  end.