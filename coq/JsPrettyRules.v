Require Import JsPreliminary JsPreliminaryAux JsPrettyInterm (* JsPrettyIntermAux *).

(**************************************************************)
(** ** Implicit Types, same as in JsSemanticsDefs *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type Vs : list value.
Implicit Type r : ref.
Implicit Type T : type.

Implicit Type x : prop_name.
Implicit Type m : mutability.
Implicit Type A : prop_attributes.
Implicit Type An : prop_descriptor.
Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type D : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.

Implicit Type res : res.
Implicit Type R : ret.
Implicit Type o : out.



(**************************************************************)
(**************************************************************)
(**************************************************************)
(** ** TODO *)



(**************************************************************)
(**************************************************************)
(**************************************************************)


Parameter alloc_primitive_value :
  state -> value -> state -> object_loc -> Prop.
Parameter basic_value_convertible_to_object : value -> Prop.

(**************************************************************)
(** ** arguments_from. TODO: move! *)

Inductive arguments_from : list value -> list value -> Prop :=
 | arguments_from_nil : forall Vs,
      arguments_from Vs nil
 | arguments_from_undef : forall Vs: list value,
      arguments_from nil Vs ->
      arguments_from nil (undef::Vs)
 | arguments_from_cons : forall Vs1 Vs2 v,
      arguments_from Vs1 Vs2 ->
      arguments_from (v::Vs1) (v::Vs2).


(**************************************************************)
(** ** Reduction rules for programs *)

Inductive red_prog : state -> execution_ctx -> ext_prog -> out -> Prop :=

  (** Generic abort rule *)

  | red_prog_abort : forall S C p o,
      out_of_ext_prog p = Some o ->
      abort o ->
      red_prog S C p o

  (** Statements *)

  | red_prog_stat : forall S C t o,
      red_stat S C t o ->
      red_prog S C (prog_stat t) o

  (** Sequence *)

  | red_prog_seq : forall S C p1 p2 o1 o,
      red_prog S C p1 o1 ->
      red_prog S C (prog_seq_1 o1 p2) o ->
      red_prog S C (prog_seq p1 p2) o

  | red_prog_seq_1 : forall S0 S re C p2 o,
      red_prog S C p2 o ->
      red_prog S C (prog_seq_1 (out_ter S re) p2) o

  (* TODO: red_prog_function_decl ? *)


(**************************************************************)
(** ** Reduction rules for statements *)

with red_stat : state -> execution_ctx -> ext_stat -> out -> Prop :=

  (** Generic abort rule *)

  | red_stat_abort : forall S C text o,
      out_of_ext_stat text = Some o ->
      ~ abort_intercepted text o ->
      abort o ->
      red_stat S C text o

  (** Expression *)

  | red_stat_expr : forall S C e o,
      red_expr S C (spec_expr_get_value e) o ->
      red_stat S C (stat_expr e) o

  (** Sequence *)

  | red_stat_seq : forall S C t1 t2 o1 o,
      red_stat S C t1 o1 ->
      red_stat S C (stat_seq_1 o1 t2) o ->
      red_stat S C (stat_seq t1 t2) o

  | red_stat_seq_1 : forall S0 S C (R1:ret_or_empty) t2 o2 o,
      red_stat S C t2 o2 ->
      red_stat S0 C (stat_seq_2 R1 o2) o ->
      red_stat S0 C (stat_seq_1 (out_ter S R1) t2) o

  | red_stat_seq_2 : forall S0 S C (R1 R2 R:ret_or_empty),
      R = (If R2 = ret_empty then R1 else R2) ->
      red_stat S0 C (stat_seq_2 R1 (out_ter S R2)) (out_ter S R)

  (** Variable declaration *)

  (* Old def *)
  (* 
  | red_stat_var_decl_none : forall S C x,
      red_stat S C (stat_var_decl x None) (out_ter S undef)

  (* TODO: red_stat_var_decl_some: can we justify that this is equivalent to the spec ?*)
  | red_stat_var_decl_some : forall S C x e o1 o,
      red_expr S C (expr_assign (expr_variable x) None e) o1 ->
      red_stat S C (stat_var_decl_1 o1) o ->
      red_stat S C (stat_var_decl x (Some e)) o

  | red_stat_var_decl_1 : forall S0 S r1 C,
      red_stat S0 C (stat_var_decl_1 (out_ter S r1)) (out_ter S undef)
  *)

  | red_stat_var_decl_nil : forall S C, 
      red_stat S C (stat_var_decl nil) (out_ter S ret_empty)

  | red_stat_var_decl_cons : forall S C o o1 d ds, 
      red_stat S C (stat_var_decl_item d) o1 ->
      red_stat S C (stat_var_decl_1 o1 ds) o ->
      red_stat S C (stat_var_decl (d::ds)) o

  | red_stat_var_decl_1 : forall S S0 C ds o R, 
      red_stat S C (stat_var_decl ds) o ->
      red_stat S0 C (stat_var_decl_1 (out_ter S R) ds) o

  (* Daniele: should return undefined instead of x? *)
  | red_stat_var_decl_item_none : forall S C x, 
      red_stat S C (stat_var_decl_item (x,None)) (out_ter S (*x*) undef)

  | red_stat_var_decl_item_some : forall S C x e o o1, 
      red_expr S C (identifier_resolution C x) o1 ->
      red_stat S C (stat_var_decl_item_1 x o1 e) o ->
      red_stat S C (stat_var_decl_item (x,Some e)) o

  | red_stat_var_decl_item_1 : forall S S0 C x e o o1 r, 
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_var_decl_item_2 x r o1) o ->
      red_stat S0 C (stat_var_decl_item_1 x (out_ter S r) e) o

  | red_stat_var_decl_item_2 : forall S S0 C r v o o1 x,  
      red_expr S C (spec_put_value r v) o1 ->
      red_stat S C (stat_var_decl_item_3 x o1) o ->
      red_stat S0 C (stat_var_decl_item_2 x r (out_ter S v)) o
  
  (* Daniele: should return undefined instead of x? *)
  | red_stat_var_decl_item_3 : forall S S0 C x r R, 
      red_stat S0 C (stat_var_decl_item_3 x (out_ter S R)) (out_ter S (*x*) undef)

  (** If statement *)
 
  | red_stat_if : forall S C e1 t2 t3opt o,
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_boolean (fun v => stat_if_1 v t2 t3opt)) o ->
      red_stat S C (stat_if e1 t2 t3opt) o

  | red_stat_if_1_true : forall S C t2 t3opt o,
      red_stat S C t2 o ->
      red_stat S C (stat_if_1 true t2 t3opt) o

  | red_stat_if_1_false : forall S C t2 t3 o,
      red_stat S C t3 o ->
      red_stat S C (stat_if_1 false t2 (Some t3)) o

  | red_stat_if_1_false_implicit : forall S C t2,
      red_stat S C (stat_if_1 false t2 None) (out_ter S undef)

  (** While statement *)

  | red_stat_while : forall S C e1 t2 o o1,
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_boolean (stat_while_1 e1 t2)) o ->
      red_stat S C (stat_while e1 t2) o

  | red_stat_while_1_false : forall S C e1 t2,
      red_stat S C (stat_while_1 e1 t2 false) (out_ter S undef)

  | red_stat_while_1_true : forall S0 S C e1 t2 o o1,
      red_stat S C t2 o1 ->
      red_stat S C (stat_while_2 e1 t2 o1) o ->
      red_stat S0 C (stat_while_1 e1 t2 true) o

  | red_stat_while_2 : forall S0 S C e1 t2 re o,
      red_stat S C (stat_while e1 t2) o ->
      red_stat S0 C (stat_while_2 e1 t2 (out_ter S re)) o
    (* TODO: handle break and continue in while loops *)
    
(**------ begin under dvpt --------*)

(* --which version to keep ??

  (** For-in statement *)

  | red_stat_for_in_2_null_or_undef : forall S0 S C e1 t v1 o,
      v1 = null \/ v1 = undef ->
      (* todo: replace premise with   [is_null_or_undef v1] *)
      red_stat S0 C (stat_for_in_2 e1 t (out_ter S v1)) (out_ter S undef)
      
  | red_stat_for_in_2_else : forall o1 S0 S C e1 t v1 o,
      v1 <> null /\ v1 <> undef ->
      (* todo: replace premise with  [~ is_null_or_undef v1] *)
      red_expr S C (spec_to_object v1) o1 ->
      red_stat S C (stat_for_in_3 e1 t o1) o ->
      red_stat S0 C (stat_for_in_2 e1 t (out_ter S v1)) o  
      
      (* todo: rename rules below *)

      (* todo: use notations : 
        Open Scope set_scope.
        x \in E   \{}  \{x}  E \u F    E = F \u \{x}   *)

*)

  (** For-in statement *)

  | red_stat_for_in : forall o1 S0 S C e1 e2 t o,
      red_expr S C (spec_expr_get_value e2) o1 ->
      red_stat S C (stat_for_in_2 e1 t o1) o ->
      red_stat S0 C (stat_for_in e1 e2 t) o

  | red_stat_for_in_3_null_undef : forall S0 S C e1 t v1 o,
      v1 = null \/ v1 = undef ->
      red_stat S0 C (stat_for_in_2 e1 t (out_ter S v1)) (out_ter S ret_or_empty_empty)

  | red_stat_for_in_4 : forall o1 S0 S C e1 t exprValue o,
      exprValue <> null /\ exprValue <> undef ->
      red_expr S C (spec_to_object exprValue) o1 ->
      red_stat S C (stat_for_in_3 e1 t o1) o ->
      red_stat S0 C (stat_for_in_2 e1 t (out_ter S exprValue)) o

  | red_stat_for_in_6a_start : forall S0 S C e1 t l initProps o,
      object_all_enumerable_properties S (value_object l) initProps ->
      red_stat S C (stat_for_in_4 e1 t l None None initProps (@empty_impl prop_name)) o ->
      red_stat S0 C (stat_for_in_3 e1 t (out_ter S l)) o

  | red_stat_for_in_6a_done : forall S C e1 t l vret lhsRef initProps visitedProps currentProps,
      object_all_enumerable_properties S (value_object l) currentProps ->
      incl_impl currentProps visitedProps ->
      red_stat S C (stat_for_in_4 e1 t l (Some vret) lhsRef initProps visitedProps) (out_ter S vret)

  (* allow possibility to skip new added property in for-in loop *)
  | red_stat_for_in_6a_skip_added_property : forall S C e1 t l vret lhsRef initProps visitedProps currentProps x o,
      object_all_enumerable_properties S (value_object l) currentProps ->
      x \in (remove_impl (remove_impl currentProps visitedProps) initProps) ->
      let newVisitedProps := union_impl (single_impl x) visitedProps in
      red_stat S C (stat_for_in_4 e1 t l vret lhsRef initProps newVisitedProps) o ->
      red_stat S C (stat_for_in_4 e1 t l vret lhsRef initProps visitedProps) o

  | red_stat_for_in_6a_select_x : forall S C e1 t l vret lhsRef initProps visitedProps currentProps x o,
      object_all_enumerable_properties S (value_object l) currentProps ->
      in_impl x (remove_impl currentProps visitedProps) ->
      let newVisitedProps := union_impl (single_impl x) visitedProps in
      red_stat S C (stat_for_in_5 e1 t l vret lhsRef initProps newVisitedProps x) o ->
      red_stat S C (stat_for_in_4 e1 t l vret lhsRef initProps visitedProps) o

  (* evaluate new lhdRef *)
  | red_stat_for_in_6b_evaluate : forall S C e1 t l vret lhdRef initProps visitedProps x o1 o,
      red_expr S C e1 o1 ->
      red_stat S C (stat_for_in_6 e1 t l vret (Some o1) initProps visitedProps x) o ->
      red_stat S C (stat_for_in_5 e1 t l vret lhdRef initProps visitedProps x) o

  (* reuse earlier lhdRef *)
  | red_stat_for_in_6b_reuse_old : forall S C e1 t l vret lhdRef initProps visitedProps x o,
      red_stat S C (stat_for_in_6 e1 t l vret (Some lhdRef) initProps visitedProps x) o ->
      red_stat S C (stat_for_in_5 e1 t l vret (Some lhdRef) initProps visitedProps x) o

  | red_stat_for_in_6c : forall S0 S C e1 t l vret lhdRef initProps visitedProps x o1 o,
      red_expr S C (spec_put_value lhdRef x) o1 ->
      red_stat S C (stat_for_in_7 e1 t l vret (Some (out_ter S lhdRef)) initProps visitedProps o1) o ->
      red_stat S0 C (stat_for_in_6 e1 t l vret (Some (out_ter S lhdRef)) initProps visitedProps x) o

  | red_stat_for_in_6d : forall S0 S C e1 t l vret lhdRef initProps visitedProps o1 o,
      red_stat S C t o1 ->
      red_stat S C (stat_for_in_8 e1 t l vret lhdRef initProps visitedProps o1) o ->
      red_stat S0 C (stat_for_in_7 e1 t l vret lhdRef initProps visitedProps (out_void S)) o

  (** Debugger statement *)
  
  | res_stat_debugger : forall S C,
      red_stat S C stat_debugger (out_ter S ret_empty)


(*-- todo: make compile following introduction of ret_or_empty (see JsSyntax) 

  | red_stat_for_in_6e : forall S0 S C e1 t l vret lhdRef initProps visitedProps res o,
      let vnew := match res with
        | res_normal R => Some R
        | _ => vret end
      in
      red_stat S C (stat_for_in_9 e1 t l vnew lhdRef initProps visitedProps res) o ->
      red_stat S0 C (stat_for_in_8 e1 t l vret lhdRef initProps visitedProps (out_ter S res)) o

  | red_stat_for_in_6f_break : forall S C e1 t l vret lhdRef initProps visitedProps label,
      (* TODO: check break label is in current label set *)
      red_stat S C (stat_for_in_9 e1 t l (Some vret) lhdRef initProps visitedProps (res_break label)) (out_ter S vret)

  | red_stat_for_in_6g_exit : forall S C e1 t l vret lhdRef initProps visitedProps res,
      (* TODO: check continue label is in current label set *)
      ~ (is_res_break res) /\ ~ (is_res_continue res) /\ ~ (is_res_normal res) ->
      red_stat S C (stat_for_in_9 e1 t l vret lhdRef initProps visitedProps res) (out_ter S res)

  | red_stat_for_in_6g_continue : forall o1 S C e1 t l vret lhdRef initProps visitedProps res o,
     (* TODO: check continue label is in current label set *)
      ~ (is_res_break res) /\ ((is_res_continue res) \/ (is_res_normal res)) ->
      red_stat S C (stat_for_in_4 e1 t l vret lhdRef initProps visitedProps) o ->
      red_stat S C (stat_for_in_9 e1 t l vret lhdRef initProps visitedProps res) o  

-- end todo *) 

(**------ end under dvpt --------*)

  (** With statement *)

  | red_stat_with : forall S C e1 t2 o,
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_object (stat_with_1 t2)) o ->
      red_stat S C (stat_with e1 t2) o

  | red_stat_with_1 : forall S S' C t2 l o lex lex' s' C',
      lex = execution_ctx_lexical_env C ->
      (lex',S') = lexical_env_alloc_object S lex l provide_this_true ->
      C' = execution_ctx_with_lex_this C lex' l ->
      red_stat S' C' t2 o ->
      red_stat S C (stat_with_1 t2 l) o

 (** Throw statement *)

  | red_stat_throw : forall S C e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_throw_1 o1) o ->
      red_stat S C (stat_throw e) o

  | red_stat_throw_1 : forall S0 S C v,
      red_stat S0 C (stat_throw_1 (out_ter S v)) (out_ter S (res_throw v))

 (** Return statement *)
  
  | red_stat_return_none : forall S C,
      red_stat S C (stat_return None) (out_ter S (res_return undef))

  | red_stat_return_some : forall S C e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_return_1 o1) o ->
      red_stat S C (stat_return (Some e)) o

  | red_stat_return_some_1 : forall S0 S C v,
      red_stat S0 C (stat_return_1 (out_ter S v)) (out_ter S (res_return v))

  (** Break statement *)

  | red_stat_break_none : forall S C,
      red_stat S C (stat_break None) (out_ter S (res_break None))

  | red_stat_break_some : forall S C s,
      red_stat S C (stat_break (Some s)) (out_ter S (res_break (Some s)))

  (** Continue statement *)

  | red_stat_continue_none : forall S C,
      red_stat S C (stat_continue None) (out_ter S (res_continue None))

  | red_stat_continue_some : forall S C s,
      red_stat S C (stat_continue (Some s)) (out_ter S (res_continue (Some s)))

  (** Try statement *)

  | red_stat_try : forall S C t co fio o o1, (* TODO: rename co and fio *)
      red_stat S C t o1 ->
      red_stat S C (stat_try_1 o1 co fio) o ->
      red_stat S C (stat_try t co fio) o

  | red_stat_try_1_no_catch : forall S0 S C re fio o,
      red_stat S0 C (stat_try_3 (out_ter S re) fio) o ->
      red_stat S0 C (stat_try_1 (out_ter S re) None fio) o

  | red_stat_try_1_catch_no_throw : forall S0 S C re x t1 fio o,
      ~ is_res_throw re ->
      red_stat S0 C (stat_try_3 (out_ter S re) fio) o ->
      red_stat S0 C (stat_try_1 (out_ter S re) (Some (x,t1)) fio) o

  | red_stat_try_1_catch_throw : forall S0 S S' C lex lex' oldlex L x v t1 fio o1 o,
      lex = execution_ctx_lexical_env C ->
      (lex',S') = lexical_env_alloc_decl S lex ->
      lex' = L::oldlex -> (* Note: oldlex in fact equal to lex *)
      (* TODO: we would be closer to the spec in red_stat_try_1_catch_throw
         if lexical environments were not lists, but instead objects with a parent field *)
      red_expr S' C (spec_env_record_create_set_mutable_binding L x None v throw_irrelevant) o1 ->
      red_stat S' C (stat_try_2 o1 lex' t1 fio) o ->
      red_stat S0 C (stat_try_1 (out_ter S (res_throw v)) (Some (x,t1)) fio) o

  | red_stat_try_2_after_catch_throw : forall C C' S0 S lex' t1 fio o o1,
      C' = execution_ctx_with_lex C lex' ->
      red_stat S C' t1 o1 ->
      red_stat S C' (stat_try_3 o1 fio) o ->
      red_stat S0 C (stat_try_2 (out_void S) lex' t1 fio) o

  | red_stat_try_3_no_finally : forall S C o,
      red_stat S C (stat_try_3 o None) o

  | red_stat_try_3_finally : forall S0 S1 C t1 re o o1,
      red_stat S1 C t1 o1 ->
      red_stat S1 C (stat_try_4 re o1) o ->
      red_stat S0 C (stat_try_3 (out_ter S1 re) (Some t1)) o

  | red_stat_try_4_after_finally : forall S0 S C re rt,
      red_stat S0 C (stat_try_4 re (out_ter S (res_normal rt))) (out_ter S re)

  (** Skip statement *)

  | red_stat_skip : forall S C,
      red_stat S C stat_skip (out_ter S ret_empty)

  (* Auxiliary forms : [spec_expr_get_value] plus a type conversion 
     for statements *)

  | red_spec_expr_get_value_conv_stat : forall S C e sc K o o1, 
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (spec_expr_get_value_conv_stat_1 o1 sc K) o ->
      red_stat S C (spec_expr_get_value_conv_stat e sc K) o

  | red_spec_expr_get_value_conv_stat_1 : forall S0 S C sc K v o o1,
      red_expr S C (sc v) o1 ->
      red_stat S C (spec_expr_get_value_conv_stat_2 o1 K) o ->
      red_stat S0 C (spec_expr_get_value_conv_stat_1 (out_ter S v) sc K) o

  | red_spec_expr_get_value_conv_stat_2 : forall S0 S C K v o,
      red_stat S C (K v) o ->
      red_stat S0 C (spec_expr_get_value_conv_stat_2 (out_ter S v) K) o


(**************************************************************)
(** ** Reduction rules for expressions *)

with red_expr : state -> execution_ctx -> ext_expr -> out -> Prop :=

  (** Generic abort rule *)

  | red_expr_abort : forall S C eext o,
      out_of_ext_expr eext = Some o ->
      abort o ->
      red_expr S C eext o

  (** Reduction of lists of expressions *)

  | red_expr_list_then : forall S C K es o,
      red_expr S C (expr_list_then_1 K nil es) o ->
      red_expr S C (expr_list_then K es) o

  | red_expr_list_then_1_nil : forall S C K vs o,
      red_expr S C (K vs) o ->
      red_expr S C (expr_list_then_1 K vs nil) o

  | red_expr_list_then_1_cons : forall S C K vs es e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_expr S C (expr_list_then_2 K vs o1 es) o ->
      red_expr S C (expr_list_then_1 K vs (e::es)) o

  | red_expr_list_then_2 : forall S0 S C K v vs es o,
      red_expr S C (expr_list_then_1 K (vs&v) es) o ->
      red_expr S0 C (expr_list_then_2 K vs (out_ter S v) es) o

  (** This construct *)

  | red_expr_this : forall S C v,
      v = execution_ctx_this_binding C ->
      red_expr S C expr_this (out_ter S v)

  (** Identifier *)

  | red_expr_variable : forall S C x o,
      red_expr S C (identifier_resolution C x) o ->
      red_expr S C (expr_variable x) o

  (** Literal *)

  | red_expr_literal : forall S C s i v,
      v = convert_literal_to_prim i ->
      red_expr S C (expr_literal i) (out_ter S v)

  (** Object initializer *)
  
  (* Allocate a new Object, then pass the adress  
     and the list of propdef to [expr_object_1] *)
  | red_expr_object : forall S C o pds, 
      red_expr S C (spec_new_object (fun l => expr_object_1 l pds) ) o ->
      red_expr S C (expr_object pds) o
              
  (* No propdefs. Return the empty object *)
  | red_expr_object_1_nil : forall S C l, 
      red_expr S C (expr_object_1 l nil) (out_ter S l)
  
  (* Propdefs are given. Convert the first propname to
     string, then call [expr_obj_2] to evaluate the propbody. *)
  | red_expr_object_1_cons : forall S C x l pn pb pds o, 
      x = string_of_propname pn ->
      red_expr S C (expr_object_2 l x pb pds) o ->
      red_expr S C (expr_object_1 l ((pn,pb)::pds)) o

  (* --- value --- *)
  (* If the propbody is an expression we evaluate it *)
  | red_expr_object_2_val : forall S C e o o1 l x pds, 
      red_expr S C (spec_expr_get_value e) o1 ->
      red_expr S C (expr_object_3_val l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_val e) pds) o

  (* If the expression terminates then we create a prop descriptor *)
  | red_expr_object_3_val : forall S S0 C l x A v o pds,
      A = prop_attributes_create_data v true true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_val l x (out_ter S v) pds) o

  (* --- get --- *)
  (* If the propbody is a getter, we evaluate the function definition *)
  
  | red_expr_object_2_get : forall S C bd l x o o1 pds,
      red_expr S C (spec_create_new_function_in C nil bd) o1 ->
      red_expr S C (expr_object_3_get l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_get bd) pds) o
  
  (* If the function def terminates, we create an accessor *)
  | red_expr_object_3_get : forall S S0 C A l x v pds o,  
      A = prop_attributes_create_accessor_opt None (Some v) true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_get l x (out_ter S v) pds) o

  (* --- set --- *)
  (* If the propbody is a setter, we evaluate the function definition *)
  | red_expr_object_2_set : forall S S0 C A l x v pds o o1 bd args,
      red_expr S C (spec_create_new_function_in C args bd) o1 ->
      red_expr S C (expr_object_3_set l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_set args bd) pds) o

  (* If the function def terminates, we create an accessor *)
  | red_expr_object_3_set : forall S S0 C A l x v pds o,
      A = prop_attributes_create_accessor_opt (Some v) None true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_set l x (out_ter S v) pds) o
  
  (* --- Add new property to the object --- *)
  (* Add the new property into the object *)
  | red_expr_object_4 : forall S S0 C A l x v pds o o1,
      red_expr S C (spec_object_define_own_prop l x A false) o1 ->
      red_expr S C (expr_object_5 l pds o1) o ->
      red_expr S C (expr_object_4 l x A pds) o

  (* If the property was added succesfully, we continue 
     to the next one. *)
  | red_expr_object_5 : forall S S0 R C A l x v pds o,
      red_expr S C (expr_object_1 l pds) o ->
      red_expr S0 C (expr_object_5 l pds (out_ter S R)) o   

(*---begin to clean ---*)

  (*----- TOCLEAN---*)

  (** Array initializer [TODO] *)

  (** Object initializer *)

  (*| red_expr_object : forall S0 S1 C l lx le lxe o,
      object_fresh S0 l ->
      S1 = alloc_obj S0 l loc_obj_proto ->
      (lx,le) = LibList.split lxe ->
      red_expr S1 C (expr_list_then (expr_object_1 l lx) le) o ->
      red_expr S0 C (expr_object lxe) o *)

  (*| red_expr_object_1 : forall S0 S1 C l lx lv lfv,
      Forall3 (fun x v xv => xv = (field_normal x,v)) lx lv lfv ->
      S1 = write_fields S0 l lfv ->
      red_expr S0 C (expr_object_1 l lx lv) (out_ter S1 l) *)

  (** Function expression *)

  | red_expr_function_unnamed : forall S C args bd o,
      red_expr S C (spec_creating_function_object args bd (execution_ctx_lexical_env C) (function_body_is_strict bd)) o ->
      red_expr S C (expr_function None args bd) o 

  | red_expr_function_named : forall lex' S' L lextail E o1 S C s args bd o,
      (lex', S') = lexical_env_alloc_decl S (execution_ctx_lexical_env C) ->
      lex' = L :: lextail ->
      env_record_binds S' L E ->
      red_expr S' C (spec_env_record_create_immutable_binding L s) o1 ->
      red_expr S' C (expr_function_1 s args bd L lex' o1) o -> 
      red_expr S C (expr_function (Some s) args bd) o 
      
  | red_expr_function_named_1 : forall o1 S0 S C s args bd L scope o,
      red_expr S C (spec_creating_function_object args bd scope (function_body_is_strict bd)) o1 ->
      red_expr S C (expr_function_2 s L o1) o ->
      red_expr S0 C (expr_function_1 s args bd L scope (out_void S)) o
      
  | red_expr_function_named_2 : forall o1 S0 S C s L l o,
      red_expr S C (spec_env_record_initialize_immutable_binding L s l) o1 ->
      red_expr S C (expr_function_3 l o1) o ->
      red_expr S0 C (expr_function_2 s L (out_ter S l)) o  
      
  | red_expr_function_named_3 : forall S0 S C l,
      red_expr S0 C (expr_function_3 l (out_void S)) (out_ter S l) 

  (** Access 11.2.1 *)

  | red_expr_access : forall S C e1 e2 o o1,
      red_expr S C (spec_expr_get_value e1) o1 ->
      red_expr S C (expr_access_1 o1 e2) o ->
      red_expr S C (expr_access e1 e2) o
      
  | red_expr_access_1 : forall S0 S C v o o1 e2,
      red_expr S C (spec_expr_get_value e2) o1 ->
      red_expr S C (expr_access_2 v o1) o ->
      red_expr S0 C (expr_access_1 (out_ter S v) e2) o
      
  | red_expr_access_2 : forall S0 S C v1 v2 o,
      red_expr S C (spec_convert_twice (spec_check_object_coercible v1) (spec_to_string v2) expr_access_3) o ->
      red_expr S0 C (expr_access_2 v1 (out_ter S v2)) o

  | red_expr_ext_expr_access_3 : forall S C v1 x r,
     r = ref_create_value v1 x (execution_ctx_strict C) ->
     red_expr S C (expr_access_3 v1 x) (out_ter S r)

  (** Member *)

  | red_expr_member : forall x S0 C e1 o,
      red_expr S0 C (expr_access e1 (expr_literal (literal_string x))) o ->
      red_expr S0 C (expr_member e1 x) o

  (** New *)

  (* todo : add exceptions and conversions for new and call *)

  | red_expr_new : forall S0 C e1 le2 o o1,
      red_expr S0 C (expr_basic e1) o1 ->
      red_expr S0 C (expr_new_1 o1 le2) o ->
      red_expr S0 C (expr_new e1 le2) o


  (* Daniele: we need to throw a 'TypeError' if l1 doesn't have type Object,
     and if it doesn't implement internal method ((Construct)) - ? *)
  (* Martin:  Do you then think that we should define a new extended expression
     ext_expr_new_<something> to just do the getvalue step and then match on
     its result?  I think it would be closer to the `great step' guidelines. *)
  (*| red_expr_ext_expr_new_1 : forall S0 S1 C l1 l2 s3 lx P3 le2 r1 v1 o,
      getvalue S1 r1 l1 ->
      l1 <> loc_null -> (* Martin:  This condition seems to be yielded by the next three. *)
        (* Arthur: agreed, we should be able to remove it;
           maybe it was there to insist on the fact that "new null" should raise an exn *)
      binds S1 l1 field_scope (value_scope s3) ->
      binds S1 l1 field_body (value_body lx P3) ->
      binds S1 l1 field_normal_prototype v1 ->
      l2 = obj_or_glob_of_value v1 ->
      red_expr S1 C (expr_list_then (expr_new_2 l2 (normal_body s3 lx P3)) le2) o ->
      red_expr S0 C (expr_new_1 (out_ter S1 r1) le2) o*)

  (*| red_expr_ext_expr_new_2 : forall S0 S1 S2 S3 S4 S5 C s3 l2 l3 l4 lx vs lfv ys P3 o1 o,
      object_fresh S0 l3 ->
      S1 = alloc_obj S0 l3 l2 ->
      object_fresh S1 l4 ->
      S2 = write_proto S1 l4 loc_null ->
      S3 = write S2 l4 field_this l3 ->
      arguments lx vs lfv ->
      S4 = write_fields S3 l4 lfv ->
      ys = defs_prog lx P3 ->
      S5 = reserve_local_vars S4 l4 ys ->
      red_expr S5 (l4::s3) (ext_expr_prog P3) o1 ->
      red_expr S5 C (expr_new_3 l3 o1) o ->
      red_expr S0 C (expr_new_2 l2 (normal_body s3 lx P3) vs) o*)

  (*| red_expr_ext_expr_new_3 : forall S0 S1 C r v l l0,
      getvalue S1 r v ->
      l = obj_of_value v l0 ->
      red_expr S0 C (expr_new_3 l0 (out_ter S1 r)) (out_ter S1 l)*)


  (** Call 11.2.3 *)


  | red_expr_call : forall S0 C e1 e2s o1 o2,
      red_expr S0 C e1 o1 ->
      red_expr S0 C (expr_call_1 o1 e2s) o2 ->
      red_expr S0 C (expr_call e1 e2s) o2

  | red_expr_call_1 : forall o1 S0 S C o R e2s,
      red_expr S C (spec_get_value R) o1 ->
      red_expr S C (expr_call_2 R e2s o1) o ->
      red_expr S0 C (expr_call_1 (out_ter S R) e2s) o
      
  | red_expr_call_2 : forall S0 S C o R v e2s,
      red_expr S C (expr_list_then (expr_call_3 R v) e2s) o ->
      red_expr S0 C (expr_call_2 R e2s (out_ter S v)) o
      
  | red_expr_call_3_not_object : forall S C o R v vs,
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_call_3 R v vs) o
      
  | red_expr_call_3_not_callable : forall S C o R l vs,
      ~ (is_callable S l) ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_call_3 R (value_object l) vs) o
      
  | red_expr_call_3_prop : forall v S C o r l vs,
      (is_callable S l) ->
      ref_is_property r -> 
      ref_is_value r v ->
      red_expr S C (expr_call_4 l vs (out_ter S v)) o ->
      red_expr S C (expr_call_3 (ret_ref r) (value_object l) vs) o
      
  | red_expr_call_3_env : forall L o1 S C o r l vs,
      (is_callable S l) ->
      ref_is_env_record r L -> 
      red_expr S C (spec_env_record_implicit_this_value L) o1 -> 
      red_expr S C (expr_call_4 l vs o1) o ->
      red_expr S C (expr_call_3 (ret_ref r) (value_object l) vs) o

  | red_expr_call_3_not_ref : forall S C v l vs o,
      red_expr S C (expr_call_4 l vs (out_ter S undef)) o ->
      red_expr S C (expr_call_3 (ret_value v) (value_object l) vs) o
   
  | red_expr_call_4 : forall builtin S0 S C l vs v o,
      object_call S l (Some builtin) ->
      red_expr S C (spec_call builtin (Some l) (Some v) vs) o ->
      red_expr S0 C (expr_call_4 l vs (out_ter S v)) o    
      
  (* TODO: eval call *)     
   
  (*| red_expr_call_2_eval : forall S0 C e2s l2 o,
      red_expr S0 C (expr_list_then (expr_call_3 l2 primitive_eval) e2s) o ->
      red_expr S0 C (expr_call_2 loc_eval l2 e2s) o*)

  (*| red_expr_call_3_eval : forall S0 C vs g e3 l0 o o3,
      parse g e3 ->
      red_expr S0 C e3 o3 ->
      red_expr S0 C (expr_call_4 o3) o ->
      red_expr S0 C (expr_call_3 l0 primitive_eval (g::vs)) o*)

(*---end to clean ---*)

  (** Unary op -- regular rules *)

  | red_expr_unary_op : forall S C op e o1 o,
      regular_unary_op op ->
      red_expr S C (spec_expr_get_value e) o1 ->
      red_expr S C (expr_unary_op_1 op o1) o ->
      red_expr S C (expr_unary_op op e) o

  | red_expr_unary_op_1 : forall S0 S C op v o,
      red_expr S C (expr_unary_op_2 op v) o ->
      red_expr S0 C (expr_unary_op_1 op (out_ter S v)) o

  (** Unary op : delete *)

  | red_expr_delete : forall S C e o1 o,
      red_expr S C e o1 ->
      red_expr S C (expr_delete_1 o1) o ->
      red_expr S C (expr_unary_op unary_op_delete e) o

  | red_expr_delete_1_value : forall S0 S C v,
      red_expr S0 C (expr_delete_1 (out_ter S (ret_value v))) (out_ter S true)

  | red_expr_delete_1_ref_property : forall S0 S C r v o1 o,
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (expr_delete_2 (ref_name r) (ref_strict r) o1) o ->
      red_expr S0 C (expr_delete_1 (out_ter S (ret_ref r))) o

  | red_expr_delete_2 : forall S0 S C x l bstrict o,
      red_expr S C (spec_object_delete l x bstrict) o ->
      red_expr S0 C (expr_delete_2 x bstrict (out_ter S l)) o

  | red_expr_delete_1_ref_env_record : forall S0 S C r L o,
      ref_is_env_record r L ->
      red_expr S C (expr_delete_3 r L (ref_strict r)) o ->
      red_expr S0 C (expr_delete_1 (out_ter S (ret_ref r))) o

  | red_expr_delete_3_nonstrict : forall S C r L o,
      red_expr S C (spec_env_record_delete_binding L (ref_name r)) o ->
      red_expr S C (expr_delete_3 r L false) o 
    
  (** Unary op : void *)

  | red_expr_unary_op_void : forall S C v,
      red_expr S C (expr_unary_op_2 unary_op_void v) (out_ter S undef)

  (** Unary op : typeof *)

  | red_expr_typeof : forall S C e o1 o,
      red_expr S C e o1 ->
      red_expr S C (expr_typeof_1 o1) o ->
      red_expr S C (expr_unary_op unary_op_typeof e) o

  | red_expr_typeof_1_unresolvable : forall S0 S r C,
      ref_is_unresolvable r ->
      red_expr S0 C (expr_typeof_1 (out_ter S (ret_ref r))) (out_ter S "undefined")

  | red_expr_typeof_1_resolvable : forall S0 S C R o1 o,
      red_expr S C (spec_get_value R) o1 ->
      red_expr S C (expr_typeof_2 o1) o ->
      red_expr S0 C (expr_typeof_1 (out_ter S R)) o

  | red_expr_typeof_2 : forall S0 S s C v o,
      s = typeof_value S v ->
      red_expr S0 C (expr_typeof_2 (out_ter S v)) (out_ter S s)

  (** Unary op : pre/post incr/decr *)

  | red_expr_prepost : forall S C op e o1 o,
      prepost_unary_op op ->
      red_expr S C e o1 ->
      red_expr S C (expr_prepost_1 op o1) o ->
      red_expr S C (expr_unary_op op e) o

  | red_expr_prepost_1_valid : forall S0 S C R op o1 o,
      red_expr S C (spec_get_value R) o1 ->
      red_expr S C (expr_prepost_2 op R o1) o ->
      red_expr S0 C (expr_prepost_1 op (out_ter S R)) o
 
  | red_expr_prepost_2 : forall S0 S C R op v o1 o,    
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (expr_prepost_3 op R o1) o ->
      red_expr S0 C (expr_prepost_2 op R (out_ter S v)) o
 
  | red_expr_prepost_3 : forall S0 S C R op number_op is_pre v n1 n2 o1 o,  
      prepost_op op number_op is_pre ->
      n2 = number_op n1 ->
      v = prim_number (if is_pre then n2 else n1) ->
      red_expr S C (spec_put_value R n2) o1 ->
      red_expr S C (expr_prepost_4 v o1) o ->
      red_expr S0 C (expr_prepost_3 op R (out_ter S n1)) o
 
  | red_expr_prepost_4 : forall S0 S C v R',  
      red_expr S0 C (expr_prepost_4 v (out_ter S R')) (out_ter S v)  (* todo: do we ignore R' ? is it out_void ? *) 

  (** Unary op : neg *)

  | red_expr_unary_op_neg : forall S C v o1 o,
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (expr_unary_op_neg_1 o1) o ->
      red_expr S C (expr_unary_op_2 unary_op_neg v) o

  | red_expr_unary_op_neg_1 : forall S0 S C n,
      red_expr S0 C (expr_unary_op_neg_1 (out_ter S n)) (out_ter S (JsNumber.neg n))

  (** Unary op : bitwise not *)

  | red_expr_unary_op_bitwise_not : forall S C v o,
      red_expr S C (spec_to_int32 v expr_unary_op_bitwise_not_1) o ->
      red_expr S C (expr_unary_op_2 unary_op_bitwise_not v) o

  | red_expr_unary_op_bitwise_not_1 : forall S C k n,
      n = JsNumber.of_int (JsNumber.int32_bitwise_not k) ->
      red_expr S C (expr_unary_op_bitwise_not_1 k) (out_ter S n)

  (** Unary op : not *)

  | red_expr_unary_op_not : forall S C v o1 o,
      red_expr S C (spec_to_boolean v) o1 ->
      red_expr S C (expr_unary_op_not_1 o1) o ->
      red_expr S C (expr_unary_op_2 unary_op_not v) o

  | red_expr_unary_op_not_1 : forall S0 S C b,
      red_expr S0 C (expr_unary_op_not_1 (out_ter S b)) (out_ter S (neg b))

  (** Binary op -- regular rules *)

  | red_expr_binary_op : forall S C op e1 e2 o1 o,
      regular_binary_op op ->
      red_expr S C (spec_expr_get_value e1) o1 ->
      red_expr S C (expr_binary_op_1 op o1 e2) o ->
      red_expr S C (expr_binary_op e1 op e2) o

  | red_expr_binary_op_1 : forall S0 S C op v1 e2 o2 o,
      red_expr S C (spec_expr_get_value e2) o2 ->
      red_expr S C (expr_binary_op_2 op v1 o2) o ->
      red_expr S0 C (expr_binary_op_1 op (out_ter S v1) e2) o

  | red_expr_binary_op_2 : forall S0 S C op v1 v2 o,
      red_expr S C (expr_binary_op_3 op v1 v2) o ->
      red_expr S0 C (expr_binary_op_2 op v1 (out_ter S v2)) o

  (** Binary op : addition *)
  
  | red_expr_binary_op_add : forall S C v1 v2 o,
      red_expr S C (spec_convert_twice (spec_to_primitive v1) (spec_to_primitive v2) expr_binary_op_add_1) o ->
      red_expr S C (expr_binary_op_3 binary_op_add v1 v2) o

  | red_expr_binary_op_add_1_string : forall S C v1 v2 o,
      (type_of v1 = type_string \/ type_of v2 = type_string) ->
      red_expr S C (spec_convert_twice (spec_to_string v1) (spec_to_string v2) expr_binary_op_add_string_1) o ->
      red_expr S C (expr_binary_op_add_1 v1 v2) o

  | red_expr_binary_op_add_string_1 : forall S C s1 s2 s o,
      (* TODO: fix this line s = string_concat s1 s2 ->*) (* Would [s = s1 ++ s2] be correct? -- Martin *)
      red_expr S C (expr_binary_op_add_string_1 s1 s2) (out_ter S s)

  | red_expr_binary_op_add_1_number : forall S C v1 v2 o,
      ~ (type_of v1 = type_string \/ type_of v2 = type_string) ->
      red_expr S C (spec_convert_twice (spec_to_number v1) (spec_to_number v2) (expr_puremath_op_1 JsNumber.add)) o ->
      red_expr S C (expr_binary_op_add_1 v1 v2) o

  (** Binary op : pure maths operations *)
 
  | red_expr_puremath_op : forall S C op F v1 v2 o,
      puremath_op op F ->
      red_expr S C (spec_convert_twice (spec_to_number v1) (spec_to_number v2) (expr_puremath_op_1 F)) o ->
      red_expr S C (expr_binary_op_3 op v1 v2) o

  | red_expr_puremath_op_1 : forall S C F n n1 n2,
      n = F n1 n2 ->
      red_expr S C (expr_puremath_op_1 F n1 n2) (out_ter S n)

  (** Binary op : shift operations *)

  | red_expr_shift_op : forall S C op b_unsigned F ext v1 v2 o,
      shift_op op b_unsigned F ->
      ext = (if b_unsigned then spec_to_uint32 else spec_to_int32) ->
      red_expr S C (ext v1 (expr_shift_op_1 F v2)) o ->
      red_expr S C (expr_binary_op_3 op v1 v2) o

  | red_expr_shift_op_1 : forall S C F k1 v2 o,
      red_expr S C (spec_to_uint32 v2 (expr_shift_op_2 F k1)) o ->
      red_expr S C (expr_shift_op_1 F v2 k1) o

  | red_expr_shift_op_2 : forall S C k1 k2 F n o,
      n = JsNumber.of_int (F k1 (JsNumber.modulo_32 k2)) ->
      red_expr S C (expr_shift_op_2 F k1 k2) (out_ter S n)

  (** Binary op : inequality *)

  | red_expr_inequality_op : forall S C v1 v2 op b_swap b_neg o,
      inequality_op op b_swap b_neg ->
      red_expr S C (expr_inequality_op_1 b_swap b_neg v1 v2) o ->
      red_expr S C (expr_binary_op_3 op v1 v2) o

  | red_expr_inequality_op_1 : forall S C v1 v2 b_swap b_neg o,
      red_expr S C (spec_convert_twice (spec_to_primitive v1) (spec_to_primitive v2) (expr_inequality_op_2 b_swap b_neg)) o ->
      red_expr S C (expr_inequality_op_1 b_swap b_neg v1 v2) o

  | red_expr_inequality_op_2 : forall S C (w1 w2 wa wb wr wr':prim) b (b_swap b_neg : bool),
      ((wa,wb) = if b_swap then (w2,w1) else (w1,w2)) ->
      wr = inequality_test_primitive wa wb ->
      (* Note: wr may only be true or false or undef *)
      wr' = (If wr = prim_undef then false  
            else If (b_neg = true /\ wr = true) then false
            else wr) ->
      red_expr S C (expr_inequality_op_2 b_swap b_neg w1 w2) (out_ter S wr')

  (** Binary op : instanceof *)

  | red_expr_binary_op_instanceof_non_object : forall S C v1 v2 o,
      type_of v2 <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 v2) o

  | red_expr_binary_op_instanceof_non_instance : forall S C v1 l o,
      object_has_instance S l None ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 (value_object l)) o

  | red_expr_binary_op_instanceof_normal : forall spec_has_instance_id S C v1 l o,
      object_has_instance S l (Some spec_has_instance_id) ->
      red_expr S C (spec_object_has_instance spec_has_instance_id l v1) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 (value_object l)) o

  (** Binary op : in *)

  | red_expr_binary_op_in_non_object : forall S C v1 v2 o,
      type_of v2 <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 v2) o

  | red_expr_binary_op_in_object : forall S C v1 l o1 o,
      red_expr S C (spec_to_string v1) o1 ->
      red_expr S C (expr_binary_op_in_1 l o1) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 (value_object l)) o

  | red_expr_binary_op_in_1 : forall S0 S C l x o,
      red_expr S C (spec_object_has_prop l x) o ->
      red_expr S0 C (expr_binary_op_in_1 l (out_ter S x)) o

  (** Binary op : equality/disequality *)

  | red_expr_binary_op_equal : forall S C v1 v2 o,
      red_expr S C (spec_equal v1 v2) o ->
      red_expr S C (expr_binary_op_3 binary_op_equal v1 v2) o

  | red_expr_binary_op_disequal : forall S C v1 v2 o1 o,
      red_expr S C (spec_equal v1 v2) o1 ->
      red_expr S C (expr_binary_op_disequal_1 o1) o ->
      red_expr S C (expr_binary_op_3 binary_op_disequal v1 v2) o

  | red_expr_binary_op_disequal_1 : forall S0 S C b,
      red_expr S0 C (expr_binary_op_disequal_1 (out_ter S b)) (out_ter S (negb b))

  (** Binary op : conversion steps for the abstract equality algorithm *)

  | red_spec_equal : forall S C v1 v2 T1 T2 o,
      T1 = type_of v1 ->
      T2 = type_of v2 ->
      red_expr S C (spec_equal_1 T1 T2 v1 v2) o -> 
      red_expr S C (spec_equal v1 v2) o 

  | red_spec_equal_1_same_type : forall S C v1 v2 T b,
      b = equality_test_for_same_type T v1 v2 ->
      red_expr S C (spec_equal_1 T T v1 v2) (out_ter S b)

  | red_spec_equal_1_diff_type : forall S C v1 v2 T1 T2 b ext o,
      ext =  
        (If T1 = type_null /\ T2 = type_undef then (spec_equal_2 true)
        else If T1 = type_undef /\ T2 = type_null then (spec_equal_2 true)
        else If T1 = type_number /\ T2 = type_string then (spec_equal_3 v1 spec_to_number v2)
        else If T1 = type_string /\ T2 = type_number then (spec_equal_3 v2 spec_to_number v1)
        else If T1 = type_bool then (spec_equal_3 v2 spec_to_number v1)
        else If T2 = type_bool then (spec_equal_3 v1 spec_to_number v2)
        else If (T1 = type_string \/ T1 = type_number) /\ T2 = type_object then (spec_equal_3 v1 spec_to_primitive v2)
        else If T1 = type_object /\ (T2 = type_string \/ T2 = type_number) then (spec_equal_3 v2 spec_to_primitive v1)
        else (spec_equal_2 false)) ->
      red_expr S C ext o ->
      red_expr S C (spec_equal_1 T1 T2 v1 v2) o

  | red_spec_equal_2 : forall S C b,
      red_expr S C (spec_equal_2 b) (out_ter S b)

  | red_spec_equal_3 : forall S C v1 v2 conv o2 o,
      red_expr S C (conv v2) o2 ->
      red_expr S C (spec_equal_4 v1 o2) o ->
      red_expr S C (spec_equal_3 v1 conv v2) o

  | red_spec_equal_4 : forall S0 S C v1 v2 o,
      red_expr S C (spec_equal v1 v2) o ->    
      red_expr S0 C (spec_equal_4 v1 (out_ter S v2)) o

  (** Binary op : strict equality/disequality *)

  | red_expr_binary_op_strict_equal : forall S C v1 v2 b,
      b = strict_equality_test v1 v2 ->
      red_expr S C (expr_binary_op_3 binary_op_strict_equal v1 v2) (out_ter S b)

  | red_expr_binary_op_strict_disequal : forall S C v1 v2 b,
      b = negb (strict_equality_test v1 v2) ->
      red_expr S C (expr_binary_op_3 binary_op_strict_disequal v1 v2) (out_ter S b)

  (** Binary op : bitwise op *)

  | red_expr_bitwise_op : forall S C op F v1 v2 o,
      bitwise_op op F ->
      red_expr S C (spec_to_int32 v1 (expr_bitwise_op_1 F v2)) o ->
      red_expr S C (expr_binary_op_3 op v1 v2) o

  | red_expr_bitwise_op_1 : forall S C F k1 v2 o,
      red_expr S C (spec_to_int32 v2 (expr_bitwise_op_2 F k1)) o ->
      red_expr S C (expr_bitwise_op_1 F v2 k1) o

  | red_expr_bitwise_op_2 : forall S C F k1 k2 n,
      n = JsNumber.of_int (F k1 k2) ->
      red_expr S C (expr_bitwise_op_2 F k1 k2) (out_ter S n)

  (** Binary op : lazy ops (and, or) *)

  | red_expr_binary_op_lazy : forall S C op b_ret e1 e2 o1 o,
      lazy_op op b_ret ->
      red_expr S C (spec_expr_get_value e1) o1 ->
      red_expr S C (expr_lazy_op_1 b_ret o1 e2) o ->
      red_expr S C (expr_binary_op e1 op e2) o

  | red_expr_lazy_op_1 : forall S0 S C b_ret e1 e2 v1 v o2 o1 o,
      red_expr S C (spec_to_boolean v1) o1 ->
      red_expr S C (expr_lazy_op_2 b_ret v1 o1 e2) o ->      
      red_expr S0 C (expr_lazy_op_1 b_ret (out_ter S v1) e2) o

  | red_expr_lazy_op_2_first : forall S0 S C b_ret b1 e2 v1,
      b1 = b_ret ->
      red_expr S0 C (expr_lazy_op_2 b_ret v1 (out_ter S b1) e2) (out_ter S v1)

  | red_expr_lazy_op_2_second : forall S0 S C b_ret v1 b1 e2 o, 
      b1 <> b_ret ->
      red_expr S C (spec_expr_get_value e2) o ->
      red_expr S0 C (expr_lazy_op_2 b_ret v1 (out_ter S b1) e2) o

  (** Binary op : coma *)

  | red_expr_binary_op_coma : forall S C v1 v2,
      red_expr S C (expr_binary_op_3 binary_op_coma v1 v2) (out_ter S v2)

  (** Assignment *)
  
  | red_expr_assign : forall S C opo e1 e2 o o1,
      red_expr S C e1 o1 ->
      red_expr S C (expr_assign_1 o1 opo e2) o ->
      red_expr S C (expr_assign e1 opo e2) o
 
  | red_expr_assign_1_simple : forall S0 S C R e2 o o1,
      red_expr S C (spec_expr_get_value e2) o1 ->
      red_expr S C (expr_assign_4 R o1) o ->
      red_expr S0 C (expr_assign_1 (out_ter S R) None e2) o

  | red_expr_assign_1_compound : forall S0 S C R op e2 o o1,
      red_expr S C (spec_get_value R) o1 ->
      red_expr S C (expr_assign_2 R o1 op e2) o ->
      red_expr S0 C (expr_assign_1 (out_ter S R) (Some op) e2) o

  | red_expr_assign_2 : forall S0 S C R op v1 o2 e2 o,
      red_expr S C (spec_expr_get_value e2) o2 ->
      red_expr S C (expr_assign_3 R v1 op o2) o ->
      red_expr S0 C (expr_assign_2 R (out_ter S v1) op e2) o

  | red_expr_assign_3 : forall S0 S C R op v1 v2 o1 o,
      red_expr S C (expr_binary_op_3 op v1 v2) o1 ->
      red_expr S C (expr_assign_4 R o1) o ->
      red_expr S0 C (expr_assign_3 R v1 op (out_ter S v2)) o

  | red_expr_assign_4 : forall S0 S C R v o1 o,
      red_expr S C (spec_put_value R v) o1 ->
      red_expr S C (expr_assign_5 v o1) o ->
      red_expr S0 C (expr_assign_4 R (out_ter S v)) o

  | red_expr_assign_5 : forall S0 S C R' v,
      red_expr S0 C (expr_assign_5 v (out_ter S R')) (out_ter S v)


(* --begin clean---


  | red_expr_ext_expr_assign_1 : forall S0 S1 C e2 re o o2,
      red_expr S1 C (expr_basic e2) o2 ->
      red_expr S1 C (ext_expr_assign_2 re o2) o ->
      red_expr S0 C (ext_expr_assign_1 (out_ter S1 re) None e2) o

  (* Daniele *)
  (*| red_expr_ext_expr_assign_2 : forall v S0 C re S1 r o,
      getvalue S1 r v ->
      red_expr S1 C (ext_expr_assign_3 re v) o ->
      red_expr S0 C (ext_expr_assign_2 re (out_ter S1 r)) o*)

  (* Daniele: assign_ok *)
  (*| red_expr_ext_expr_assign_3_ok : forall S0 S1 S2 s r l x v,
      S2 = update S1 l x v ->
      red_expr S0 C (ext_expr_assign_3 (Ref l x) v) (out_ter S2 v)*)

  (* Daniele: assign_error, see 11.13.1 ECMA 5 *)
  (*| red_expr_ext_expr_assign_3_error : forall S0 C re l x v,
      (ERROR_CONDITIONS re) -> (* TODO *)
      red_expr S0 C (ext_expr_assign_3 re v) (out_basic_error S0)*)

  (*| red_expr_ext_expr_assign_1_op : forall S0 S1 C op (r : reference) v e2 o o2,
      getvalue S1 r v ->
      red_expr S1 C e2 o2 ->
      red_expr S1 C (ext_expr_assign_2_op r v op o2) o ->
      red_expr S0 C (ext_expr_assign_1 (out_ter S1 r) (Some op) e2) o*)

  (*| red_expr_ext_expr_assign_2_op : forall S0 S1 S2 s op r2 l x v1 v2 v,
      getvalue S1 r2 v2 ->
      binary_op_red op S1 v1 v2 v ->
      S2 = update S1 l x v ->
      red_expr S0 C (ext_expr_assign_2_op (Ref l x) v1 op (out_ter S1 r2)) (out_ter S2 v)*)

END OF TO CLEAN----*)

(** Conditional operator *)

(* Daniele: non factorised version
  | red_expr_conditional : forall S C e1 e2 e3 o o1,
      red_expr S C (spec_expr_get_value_conv spec_to_boolean e1) o1 ->
      red_expr S C (expr_conditional_1 o1 e2 e3) o -> 
      red_expr S C (expr_conditional e1 e2 e3) o

  | red_expr_conditional_1_true : forall S S1 S2 C e1 e2 e3 o,
      red_expr S C (spec_expr_get_value e2) o ->
      red_expr S C (expr_conditional_1 (out_ter S1 true) e2 e3) o

  | red_expr_conditional_1_false : forall S S1 S2 C e1 e2 e3 o,
      red_expr S C (spec_expr_get_value e3) o ->
      red_expr S C (expr_conditional_1 (out_ter S2 false) e2 e3) o
*)

 
  | red_expr_conditional : forall S C e1 e2 e3 o o1,
      red_expr S C (spec_expr_get_value_conv spec_to_boolean e1) o1 ->
      red_expr S C (expr_conditional_1 o1 e2 e3) o ->
      red_expr S C (expr_conditional e1 e2 e3) o

  | red_expr_conditional_1' : forall S C e b e2 e3 o,
      e = (If b = true then e2 else e3) ->
      red_expr S C (spec_expr_get_value e) o ->
      red_expr S C (expr_conditional_1' (out_ter S b) e2 e3) o



(**************************************************************)
(** ** Reduction rules for specification functions *)

  (*------------------------------------------------------------*)
  (** ** Conversions *)

  (** Conversion to bool *)

  | red_spec_to_boolean : forall S C v b,
      b = convert_value_to_boolean v ->
      red_expr S C (spec_to_boolean v) (out_ter S b)

  (** Conversion to number *)

  | red_spec_to_number_prim : forall S C w n,
      n = convert_prim_to_number w ->
      red_expr S C (spec_to_number (value_prim w)) (out_ter S n)

  | red_spec_to_number_object : forall S C l o1 o,
      red_expr S C (spec_to_primitive_pref (value_object l) (Some preftype_number)) o1 ->
      red_expr S C (spec_to_number_1 o1) o ->
      red_expr S C (spec_to_number (value_object l)) o

  | red_spec_to_number_1 : forall S0 S C w n,
      n = convert_prim_to_number w ->
      red_expr S0 C (spec_to_number_1 (out_ter S w)) (out_ter S n)
      (* TODO--Note: [w] above stands for [res_normal (ret_value (value_prim w))] *)

  (** Conversion to integer *)

  | red_spec_to_integer : forall S C v o1 o,
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_to_integer_1 o1) o ->
      red_expr S C (spec_to_integer v) o

  | red_spec_to_integer_1 : forall S0 S C n n',
      n' = convert_number_to_integer n ->
      red_expr S0 C (spec_to_integer_1 (out_ter S n)) (out_ter S n')

  (** Conversion to string *)

  | red_spec_to_string_prim : forall S C w s,
      s = convert_prim_to_string w ->
      red_expr S C (spec_to_string (value_prim w)) (out_ter S s)

  | red_spec_to_string_object : forall S C l o1 o,
      red_expr S C (spec_to_primitive_pref (value_object l) (Some preftype_string)) o1 ->
      red_expr S C (spec_to_string_1 o1) o ->
      red_expr S C (spec_to_string (value_object l)) o

  | red_spec_to_string_1 : forall S0 S C w s,
      s = convert_prim_to_string w ->
      red_expr S0 C (spec_to_string_1 (out_ter S w)) (out_ter S s)
      (* TODO: note w stand for (res_normal (ret_value (value_prim w)) *)

  (** Conversion to object *)

  | red_spec_to_object_undef_or_null : forall S C v,
      v = prim_null \/ v = prim_undef ->
      red_expr S C (spec_to_object v) (out_type_error S)

  | red_spec_to_object_primitive_value : forall S C v l S',
      basic_value_convertible_to_object v -> (* TODO: define this *)
      alloc_primitive_value S v S' l -> (* TODO: define this *)
      red_expr S C (spec_to_object v) (out_ter S' l)

  | red_spec_to_object_object : forall S C l,
      red_expr S C (spec_to_object (value_object l)) (out_ter S l)

  (** Check object coercible *)

  | red_spec_check_object_coercible_undef_or_null : forall S C v,
      v = prim_null \/ v = prim_undef ->
      red_expr S C (spec_check_object_coercible v) (out_type_error S)

  | red_spec_check_object_basic : forall S C v o,
      (* TODO: add a premise to alloc a primitive object Boolean or Number or String *)
      red_expr S C (spec_check_object_coercible v) o

  | red_spec_check_object_object : forall S C l,
      red_expr S C (spec_check_object_coercible (value_object l)) (out_ter S l)

  (** Conversion to primitive *)

  | red_spec_to_primitive_pref_prim : forall S C w prefo,
      red_expr S C (spec_to_primitive_pref (value_prim w) prefo) (out_ter S w)

  | red_spec_to_primitive_pref_obj : forall S C l prefo o,
      red_expr S C (spec_to_default l prefo) o ->
      red_expr S C (spec_to_primitive_pref (value_object l) prefo) o

  (** Conversion to default value *)

  | red_spec_to_default : forall S C l prefo pref o,
      pref = unsome_default preftype_number prefo ->
      (* TODO:  unless O is a Date object (see 15.9.6), in which case pref should be preftype_string *)
      red_expr S C (spec_to_default_1 l pref (other_preftypes pref)) o ->
      red_expr S C (spec_to_default l prefo) o

  | red_spec_to_default_1 : forall S C l pref1 pref2 o,
      red_expr S C (spec_to_default_sub_1 l (method_of_preftype pref1) (spec_to_default_2 l pref2)) o ->
      red_expr S C (spec_to_default_1 l pref1 pref2) o

  | red_spec_to_default_2 : forall S C l pref2 o,
      red_expr S C (spec_to_default_sub_1 l (method_of_preftype pref2) spec_to_default_3) o ->
      red_expr S C (spec_to_default_2 l pref2) o

  | red_spec_to_default_3 : forall S C,
      red_expr S C spec_to_default_3 (out_type_error S)

  | red_spec_to_default_sub_1 : forall o1 S C l x K o,
      red_expr S C (spec_object_get l x) o1 ->
      red_expr S C (spec_to_default_sub_2 l o1 K) o ->
      red_expr S C (spec_to_default_sub_1 l x K) o

  | red_spec_to_default_sub_2_not_callable : forall S0 S C l lf K o,
      callable S lf None ->
      red_expr S C (expr_basic K) o ->
      red_expr S0 C (spec_to_default_sub_2 l (out_ter S lf) K) o

  | red_spec_to_default_sub_2_callable : forall lfo S C l lf K o builtinid o1,
      callable S lf (Some builtinid) ->
      value_object lfo = lf ->
      red_expr S C (spec_call builtinid (Some lfo) (Some lf) nil) o1 ->
      red_expr S C (spec_to_default_sub_3 o1 (expr_basic K)) o ->
      red_expr S C (spec_to_default_sub_2 l (out_ter S lf) K) o

  | red_spec_to_default_sub_3 : forall S S0 C r v K o,
      (* TODO: do we need to perform a [get_value S r v] at this point? *)
      red_expr S C (spec_to_default_sub_4 v K) o ->
      red_expr S0 C (spec_to_default_sub_3 (out_ter S r) K) o

  | red_spec_to_default_sub_4_prim : forall S C K w,
      red_expr S C (spec_to_default_sub_4 (value_prim w) K) (out_ter S w)

  | red_spec_to_default_sub_4_object : forall S C l K o,
      red_expr S C K o ->
      red_expr S C (spec_to_default_sub_4 (value_object l) K) o

  (** Auxiliary: Conversion of two values *)

  | red_expr_conv_two : forall S C ex1 ex2 o1 K o,
      red_expr S C ex1 o1 ->
      red_expr S C (spec_convert_twice_1 o1 ex2 K) o ->
      red_expr S C (spec_convert_twice ex1 ex2 K) o

  | red_expr_conv_two_1 : forall S0 S C v1 ex2 o2 K o,
      red_expr S C ex2 o2 ->
      red_expr S C (spec_convert_twice_2 o2 (K v1)) o ->
      red_expr S0 C (spec_convert_twice_1 (out_ter S v1) ex2 K) o

  | red_expr_conv_two_2 : forall S0 S C v2 K o,
      red_expr S C (K v2) o ->
      red_expr S0 C (spec_convert_twice_2 (out_ter S v2) K) o

  (** Auxiliary: Conversion of two expressions *)
(* TODO: uniform convention for convert/conv  *)

(* todo: is neeeded?
  | red_spec_expr_conv_twice : forall S C e1 e2 conv1 conv2 K o1 o,
      red_expr S C (spec_expr_get_value_1 e1) o1 ->
      red_expr S C (spec_expr_conv_twice_1 o1 e2 conv1 conv2 K) o ->
      red_expr S C (spec_expr_conv_twice e1 e2 conv1 conv2 K) o

  | red_spec_expr_conv_twice_1 : forall S0 S C v1 e2 conv1 conv2 K o2 o,
      red_expr S C (spec_expr_get_value_1 e2) o2 ->
      red_expr S C (spec_expr_conv_twice_2 v1 o2 conv1 conv2 K) o ->
      red_expr S0 C (spec_expr_conv_twice_1 (out_ter S v1) e2 conv1 conv2 K) o

  | red_spec_expr_conv_twice_2 : forall S0 S C v1 v2 conv1 conv2 K o2 o,
      red_expr S C (conv1 v1) o1 ->
      red_expr S C (spec_expr_conv_twice_3 o1 v2 conv2 K) o ->
      red_expr S0 C (spec_expr_conv_twice_2 v1 (out_ter S v2) conv1 conv2 K) o

  | red_spec_expr_conv_twice_3 : forall S0 S C v1 v2 conv2 K o2 o,
      red_expr S C (conv2 v2) o2 ->
      red_expr S C (spec_expr_conv_twice_4 o2 (K v1)) o ->
      red_expr S0 C (spec_expr_conv_twice_3 (out_ter S v1) v2 conv2 K) o

  | red_spec_expr_conv_twice_4 : forall S0 S C v2 K o,
      red_expr S C (K v2) o ->
      red_expr S0 C (spec_convert_twice_2 (out_ter S v2) K) o
*)

  (*------------------------------------------------------------*)
  (** ** Operations on objects *)

  (** Get *)
  
  | red_expr_object_get_object : forall S C l x o,
      object_get S l builtin_spec_op_object_get ->
      red_expr S C (spec_object_object_get l x) o ->
      red_expr S C (spec_object_get l x) o  
      
  | red_expr_object_get_function : forall S C l x o,
      object_get S l builtin_spec_op_function_get ->
      red_expr S C (spec_object_function_get l x) o ->
      red_expr S C (spec_object_get l x) o 

  | red_expr_object_object_get : forall An S C l x o,
      object_get_property S (value_object l) x An ->
      red_expr S C (spec_object_object_get_1 l An) o ->
      red_expr S C (spec_object_object_get l x) o

  | red_expr_object_object_get_1_undef : forall S C l,
      red_expr S C (spec_object_object_get_1 l prop_descriptor_undef) (out_ter S undef)

  | red_expr_object_object_get_1_some_data : forall S C l A v,
      prop_attributes_is_data A ->
      prop_attributes_value A = Some v ->
      red_expr S C (spec_object_object_get_1 l (prop_descriptor_some A)) (out_ter S v)

  | red_expr_object_object_get_1_some_accessor : forall S C l A o,
      prop_attributes_is_accessor A ->
      red_expr S C (spec_object_object_get_2 l (prop_attributes_get A)) o ->
      red_expr S C (spec_object_object_get_1 l (prop_descriptor_some A)) o

  | red_expr_object_object_get_2_undef : forall S C l,
      red_expr S C (spec_object_object_get_2 l (Some undef)) (out_ter S undef)

  | red_expr_object_object_get_2_getter : forall builtinid S C l f o,
      object_call S f (Some builtinid) ->
      red_expr S C (spec_call builtinid (Some f) (Some (value_object l)) nil) o ->
      red_expr S C (spec_object_object_get_2 l (Some (value_object f))) o

      (* TODO: what should we do for [spec_object_get_2 l None] ? *)
      
  | red_expr_object_function_get : forall o1 S C l x o,
      red_expr S C (spec_object_object_get l x) o1 ->
      red_expr S C (spec_object_function_get_1 l x o1) o ->
      red_expr S C (spec_object_function_get l x) o
      
  | red_expr_object_function_get_1_error : forall bd S0 S C l v o,
      object_code S l (Some bd) ->
      function_body_is_strict bd = true ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S0 C (spec_object_function_get_1 l "caller" (out_ter S v)) o
      
  | red_expr_object_function_get_1 : forall bd S0 S C l x v o,
      (object_code S l (Some bd) /\ function_body_is_strict bd = false) \/ (x <> "caller") \/ (object_code S l None) ->
      red_expr S0 C (spec_object_function_get_1 l x (out_ter S v)) (out_ter S v)

  (** Can put *)

  | red_expr_object_can_put : forall An S C l x o,
      object_get_own_property S l x An ->
      red_expr S C (spec_object_can_put_1 l x An) o ->
      red_expr S C (spec_object_can_put l x) o

  | red_expr_object_can_put_1_some : forall b An S C l x A o,
      b = isTrue (prop_attributes_is_accessor A) ->
      red_expr S C (spec_object_can_put_2 l x b) o ->
      red_expr S C (spec_object_can_put_1 l x (prop_descriptor_some A)) o

  | red_expr_object_can_put_2_true : forall b An S C l x A o,
      (b = If (prop_attributes_set A = Some undef \/ prop_attributes_set A = None) then false else true) ->
      (* TODO: need to check in a real implementation whether the line above is correct *)
      red_expr S C (spec_object_can_put_2 l x true) (out_ter S b)

  | red_expr_object_can_put_2_false : forall b S C l x A o,
      prop_attributes_is_data A -> (* Note: spec says this hypothesis is optional *)
      b = unsome_default false (prop_attributes_writable A) ->
        (* TODO: need to check in a real implementation whether the line above is correct *)
      red_expr S C (spec_object_can_put_2 l x false) (out_ter S b)

  | red_expr_object_can_put_1_undef : forall S C l x o lproto,
      object_proto S l lproto ->
      red_expr S C (spec_object_can_put_3 l x lproto) o ->
      red_expr S C (spec_object_can_put_1 l x prop_descriptor_undef) o

  | red_expr_object_can_put_3_null : forall S C l x o b,
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_3 l x null) (out_ter S b)

  | red_expr_object_can_put_3_not_null : forall S C l x o lproto Anproto,
      object_get_property S lproto x Anproto ->
      red_expr S C (spec_object_can_put_4 l Anproto) o ->
      (* Note: semantics is stuck if proto is not a location nor null *)
      red_expr S C (spec_object_can_put_3 l x lproto) o

  | red_expr_object_can_put_4_undef : forall S C l x o b,
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_4 l prop_descriptor_undef) (out_ter S b)

  | red_expr_object_can_put_4_some_accessor : forall S C l A b,
      prop_attributes_is_accessor A ->
      (b = If (prop_attributes_set A = Some undef \/ prop_attributes_set A = None) then false else true) ->
        (* TODO: need to check in a real implementation whether the line above is correct *)
        (* TODO: factorize with above *)
      red_expr S C (spec_object_can_put_4 l (prop_descriptor_some A)) (out_ter S b)

  | red_expr_object_can_put_4_some_data : forall S C l x o A bext b,
      prop_attributes_is_data A ->
      object_extensible S l bext ->
      b = (If bext = false
            then false
            else unsome_default false (prop_attributes_writable A)) ->
        (* TODO: need to check in a real implementation whether the line above is correct *)
      red_expr S C (spec_object_can_put_4 l (prop_descriptor_some A)) (out_ter S b)

  (** Put *)

  | red_expr_object_put : forall o1 S C l x v throw o,
      red_expr S C (spec_object_can_put l x) o1 ->
      red_expr S C (spec_object_put_1 l x v throw o1) o ->
      red_expr S C (spec_object_put l x v throw) o

  | red_expr_object_put_1_false : forall S C l x v throw,
      red_expr S C (spec_object_put_1 l x v throw (out_ter S false)) (out_reject S throw)

  | red_expr_object_put_1_true : forall AnOwn S C l x v throw o,
      object_get_own_property S l x AnOwn ->
      red_expr S C (spec_object_put_2 l x v throw AnOwn) o ->
      red_expr S C (spec_object_put_1 l x v throw (out_ter S true)) o

  | red_expr_object_put_2_data : forall A' S C l x v throw AnOwn o,
      prop_descriptor_is_data AnOwn -> (* Please double check:  I've replaced it from [prop_attributes_is_data]. -- Martin. *)
      A' = prop_attributes_create_value v ->
      red_expr S C (spec_object_define_own_prop l x A' throw) o ->
      red_expr S C (spec_object_put_2 l x v throw AnOwn) o

  | red_expr_object_put_2_not_data : forall AnOwn An S C l x v throw o,
      ~ prop_descriptor_is_data AnOwn -> (* Idem -- Martin. *)
      object_get_property S (value_object l) x An ->
      red_expr S C (spec_object_put_3 l x v throw An) o ->
      red_expr S C (spec_object_put_2 l x v throw AnOwn) o

  | red_expr_object_put_3_accessor : forall fsetter fsettero builtinid S C l x v throw A o,
      prop_attributes_is_accessor A ->
      Some fsetter = prop_attributes_set A ->
      (* optional thanks to the canput test: fsetter <> undef --- Arthur: I don't understand... *)
      fsetter = value_object fsettero ->
      object_call S fsettero (Some builtinid) ->
      red_expr S C (spec_call builtinid (Some fsettero) (Some (value_object l)) (v::nil)) o ->
      red_expr S C (spec_object_put_3 l x v throw A) o

  | red_expr_object_put_3_not_accessor : forall A' S C l x v throw A o,
      ~ prop_attributes_is_accessor A ->
      A' = prop_attributes_create_data v true true true ->
      red_expr S C (spec_object_define_own_prop l x A' throw) o ->
      red_expr S C (spec_object_put_3 l x v throw A) o

  (** Has property *)

  | red_expr_object_has_property : forall An S C l x b,
      object_get_property S (value_object l) x An ->
      b = isTrue (An <> prop_descriptor_undef) ->
      red_expr S C (spec_object_has_prop l x) (out_ter S b)

  (** Delete *)

  | red_expr_object_delete : forall An S C l x throw o,
      object_get_own_property S l x An ->
      red_expr S C (spec_object_delete_1 l x throw An) o ->
      red_expr S C (spec_object_delete l x throw) o

  | red_expr_object_delete_1_undef : forall S C l x throw,
      red_expr S C (spec_object_delete_1 l x throw prop_descriptor_undef) (out_ter S true)

  | red_expr_object_delete_1_some : forall b A S C l x throw o,
      b = isTrue (prop_attributes_configurable A = Some true) ->
      red_expr S C (spec_object_delete_2 l x throw b) o ->
      red_expr S C (spec_object_delete_1 l x throw (prop_descriptor_some A)) o

  | red_expr_object_delete_2_true : forall S C l x throw S',
      object_rem_property S l x S' ->
      red_expr S C (spec_object_delete_2 l x throw true) (out_ter S' true)

  | red_expr_object_delete_2_false : forall A S C l x throw S',
      red_expr S C (spec_object_delete_2 l x throw false) (out_reject S throw)

  (** Define own property *)

  | red_expr_object_define_own_property : forall oldpd extensible h' S C l x newpf throw o,(* Steps 1, 2. *)
      object_get_own_property S l x oldpd ->
      object_extensible S l extensible ->
      red_expr h' C (spec_object_define_own_prop_1 l x oldpd newpf throw extensible) o ->
      red_expr S C (spec_object_define_own_prop l x newpf throw) o

  | red_expr_object_define_own_prop_1_undef_false : forall S C l x newpf throw, (* Step 3. *)
      red_expr S C (spec_object_define_own_prop_1 l x prop_descriptor_undef newpf throw false) (out_reject S throw)

  | red_expr_object_define_own_prop_1_undef_true : forall A' S C l x newpf throw S', (* Step 4. *)
      A' = (If (prop_attributes_is_generic newpf \/ prop_attributes_is_data newpf)
        then prop_attributes_convert_to_data newpf
        else prop_attributes_convert_to_accessor newpf) ->
      object_set_property S l x A' S' ->
      red_expr S C (spec_object_define_own_prop_1 l x prop_descriptor_undef newpf throw true) (out_ter S' true)

  | red_expr_object_define_own_prop_1_includes : forall S C l x oldpf newpf throw, (* Step 6 (subsumes 5). *)
      prop_attributes_contains oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_1 l x (prop_descriptor_some oldpf) newpf throw true) (out_ter S true)

  | red_expr_object_define_own_prop_1_not_include : forall S C l x oldpf newpf throw o, (* Steps 6 else branch. *)
      ~ prop_attributes_contains oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_1 l x (prop_descriptor_some oldpf) newpf throw true) o

  | red_expr_object_define_own_prop_2_reject : forall S C l x oldpf newpf throw, (* Step 7. *)
      change_enumerable_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) (out_reject S throw)

  | red_expr_object_define_own_prop_2_not_reject : forall S C l x oldpf newpf throw o, (* Step 7 else branch. *)
      ~ change_enumerable_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_3_generic : forall S C l x oldpf newpf throw o,(* Step 8. *)
      prop_attributes_is_generic newpf ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_3_a : forall S C l x oldpf newpf throw o,(* Step 9. *)
      (prop_attributes_is_data oldpf) <> (prop_attributes_is_data newpf) ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_4a_1 : forall S C l x oldpf newpf throw, (* Step 9a. *)
      prop_attributes_configurable oldpf = Some false ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) (out_reject S throw)

  | red_expr_object_define_own_prop_4a_2 : forall changedpf S' S C l x oldpf newpf throw o, (* Step 9b, 9c. *)
      changedpf = (If (prop_attributes_is_data oldpf)
        then prop_attributes_convert_to_accessor oldpf
        else prop_attributes_convert_to_data oldpf) ->
      object_set_property S l x changedpf S' ->
      red_expr S' C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_3_b : forall S C l x oldpf newpf throw o, (* Step 10. *)
      prop_attributes_is_data oldpf ->
      prop_attributes_is_data newpf ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_4b_1 : forall S C l x oldpf newpf throw, (* Step 10a. *)
      prop_attributes_configurable oldpf = Some false ->
      change_data_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) (out_reject S throw)

  | red_expr_object_define_own_prop_4b_2 : forall S C l x oldpf newpf throw o, (* Step 10a else branch. *)
      (   (   prop_attributes_configurable oldpf = Some false
           /\ ~ change_data_attributes_on_non_configurable oldpf newpf)
      \/ (prop_attributes_configurable oldpf = Some true)) ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_3_c : forall S C l x oldpf newpf throw o, (* Step 11. *)
      prop_attributes_is_accessor oldpf ->
      prop_attributes_is_accessor newpf ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_4c_1 : forall S C l x oldpf newpf throw, (* Step 11a. *)
      prop_attributes_configurable oldpf = Some false ->
      change_accessor_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) (out_reject S throw)

   | red_expr_object_define_own_prop_4c_2 : forall S C l x oldpf newpf throw o, (* Step 11a else branch. *)
      prop_attributes_configurable oldpf = Some false ->
      ~ change_accessor_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) o

  | red_expr_object_define_own_prop_5 : forall changedpf S C l x oldpf newpf throw h', (* Step 12, 13. *)
      changedpf = prop_attributes_transfer oldpf newpf ->
      object_set_property S l x changedpf h' ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) (out_ter h' true)
      
  (** Has Instance *)
  | red_expr_object_has_instance_prim : forall S C l w o,
      red_expr S C (spec_object_has_instance builtin_spec_op_function_has_instance l (value_prim w)) (out_ter S false)
  
  | red_expr_object_has_instance_obj : forall o1 S C l lv o,
      red_expr S C (spec_object_get l "prototype") o1 ->
      red_expr S C (spec_object_has_instance_1 lv o1) o ->
      red_expr S C (spec_object_has_instance builtin_spec_op_function_has_instance l (value_object lv)) o
      
  | red_expr_object_has_instance_1_prim : forall S0 S C lv v o,
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S v)) o
      
  | red_expr_object_has_instance_1_false : forall S0 S C lv lo,
      object_proto S lv null ->     
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) (out_ter S false)
      
  | red_expr_object_has_instance_1_true : forall proto lo S0 S C lv,
      object_proto S lv (value_object proto) ->
      proto = lo ->     
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) (out_ter S true)
      
   | red_expr_object_has_instance_1 : forall proto lo S0 S C lv v o,
      object_proto S lv (value_object proto) ->
      proto <> lo ->     
      red_expr S C (spec_object_has_instance_1 proto (out_ter S (value_object lo))) o ->
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) o
  
   

  (*------------------------------------------------------------*)
  (** ** Operations on references *)

  (** Get value on a reference *)

  | red_expr_ref_get_value_value : forall S C v, (* Step 1. *)
      red_expr S C (spec_get_value (ret_value v)) (out_ter S v)

  | red_expr_ref_get_value_ref_a : forall S C r, (* Steps 2 and 3. *)
      ref_is_unresolvable r ->
      red_expr S C (spec_get_value (ret_ref r)) (out_ref_error S)

  | red_expr_ref_get_value_ref_b: forall ext_get v S C r o, (* Step 4. *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ext_get = (If ref_has_primitive_base r
        then spec_object_get_special
        else spec_object_get) ->
      red_expr S C (ext_get v (ref_name r)) o ->
      red_expr S C (spec_get_value (ret_ref r)) o

  | red_expr_ref_get_value_ref_c : forall L S C r o, (* Step 5. *)
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_get_binding_value L (ref_name r) (ref_strict r)) o ->
      red_expr S C (spec_get_value (ret_ref r)) o

  | red_expr_object_get_special : forall o1 S C v x o,
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (spec_object_get_special_1 x o1) o ->
      red_expr S C (spec_object_get_special v x) o

  | red_expr_object_get_special1 : forall S0 C x S l o,
      red_expr S C (spec_object_get l x) o ->
      red_expr S0 C (spec_object_get_special_1 x (out_ter S (value_object l))) o

  (** Auxiliary: combine [red_expr] and [get_value] *)

  | red_spec_expr_get_value : forall S C e o o1,
      red_expr S C e o1 ->
      red_expr S C (spec_expr_get_value_1 o1) o ->
      red_expr S C (spec_expr_get_value e) o

  | red_spec_expr_get_value_1 : forall S0 S C R o,
      red_expr S C (spec_get_value R) o ->
      red_expr S0 C (spec_expr_get_value_1 (out_ter S R)) o

  (** Auxiliary: combine [red_expr] and [get_value] and a conversion *)

  | red_spec_expr_get_value_conv : forall S C e conv o o1,
      (* red_expr S C e o1 -> *) (* Daniele: it didn't really call get_value before so I changed it. Is it ok? *)                               
      red_expr S C (spec_expr_get_value e) o1 -> 
      red_expr S C (spec_expr_get_value_conv_1 conv o1) o -> 
      red_expr S C (spec_expr_get_value_conv conv e) o

  | red_spec_expr_get_value_conv_1 : forall S0 S C conv v o,
      red_expr S C (conv v) o ->
      red_expr S0 C (spec_expr_get_value_conv_1 conv (out_ter S v)) o

  (** Put value on a reference *)

  | red_expr_ref_put_value_value : forall S C v vnew, (* Step 1. *)
      red_expr S C (spec_put_value (ret_value v) vnew) (out_ref_error S) 
    
  | red_expr_ref_put_value_ref_a_1 : forall S C r vnew, (* Steps 2 and 3a. *)
      ref_is_unresolvable r ->
      ref_strict r = true ->
      red_expr S C (spec_put_value (ret_ref r) vnew) (out_ref_error S) 

  | red_expr_ref_put_value_ref_a_2 : forall o S C r vnew, (* Steps 2 and 3b. *)
      ref_is_unresolvable r ->
      ref_strict r = false ->
      red_expr S C (spec_object_put builtin_global (ref_name r) vnew throw_false) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o 

  (* ARTHUR::
  | red_expr_ref_put_value_ref_b : forall v ext_put S C r vnew o, (* Step 4. *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ext_put = (If ref_has_primitive_base r
        then spec_object_put_special
        else spec_object_put) ->
      red_expr S C (ext_put v (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o
  *)

  (* Can we do with just one rule? *)
  | red_expr_ref_put_value_ref_b_special : forall v S C r vnew o, (* Step 4. *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ref_has_primitive_base r  ->
      red_expr S C (spec_object_put_special v (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o

  | red_expr_ref_put_value_ref_b : forall l S C r vnew o, (* Step 4. *)
      ref_is_property r ->
      ref_base r = ref_base_type_value (value_object l) ->
      ~ ref_has_primitive_base r ->
      red_expr S C (spec_object_put l (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o
      
  | red_expr_ref_put_value_ref_c : forall L S C r vnew o, (* Step 5. *)     
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_set_mutable_binding L (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o  
  
  (*------------------------------------------------------------*)
  (** ** Operations on environment records *)

  (** Has binding *)

  | red_expr_env_record_has_binding : forall S C L x o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_has_binding_1 L x E) o ->
      red_expr S C (spec_env_record_has_binding L x) o

  | red_expr_env_record_has_binding_1_decl : forall S C L x D b,
      b = isTrue (decl_env_record_indom D x) ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_decl D)) (out_ter S b)

  | red_expr_env_record_has_binding_1_obj : forall S C L x l pt o,
      red_expr S C (spec_object_has_prop l x) o ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_object l pt)) o

  (** Create immutable binding *)

  | red_expr_env_record_create_immutable_binding : forall D S C L x S',
      env_record_binds S L (env_record_decl D) -> (* Note: the spec asserts that there is a binding *)
      ~ decl_env_record_indom D x ->
      S' = env_record_write_decl_env S L x mutability_uninitialized_immutable undef ->
      red_expr S C (spec_env_record_create_immutable_binding L x) (out_void S')

  (** Initialize immutable binding *)

  | red_expr_env_record_initialize_immutable_binding : forall D v_old S C L x v S',
      env_record_binds S L (env_record_decl D) ->
      decl_env_record_binds D x mutability_uninitialized_immutable v_old -> (* Note: v_old is always undef *)
      S' = env_record_write_decl_env S L x mutability_immutable v ->
      red_expr S C (spec_env_record_initialize_immutable_binding L x v) (out_void S')

  (** Create mutable binding *)

  | red_expr_env_record_create_mutable_binding : forall S C L x deletable_opt deletable o E,
      deletable = unsome_default false deletable_opt ->
      env_record_binds S L E ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable E) o ->
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o

  | red_expr_env_record_create_mutable_binding_1_decl_indom : forall S C L x deletable D S',
      ~ decl_env_record_indom D x ->
      S' = env_record_write_decl_env S L x (mutability_of_bool deletable) undef ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_decl D)) (out_void S')

  | red_expr_env_record_create_mutable_binding_1_obj : forall o1 S C L x deletable l pt o,
      red_expr S C (spec_object_has_prop l x) o1 ->
      red_expr S C (spec_env_record_create_mutable_binding_2 L x deletable l o1) o ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_object l pt)) o

  | red_expr_env_record_create_mutable_binding_obj_2 : forall A S0 C L x deletable l S o,
      A = prop_attributes_create_data undef true true deletable ->
      red_expr S C (spec_object_define_own_prop l x A throw_true) o ->
      red_expr S0 C (spec_env_record_create_mutable_binding_2 L x deletable l (out_ter S false)) o

  (** Set mutable binding *)

  | red_expr_env_record_set_mutable_binding : forall S C L x v strict o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v strict E) o ->
      red_expr S C (spec_env_record_set_mutable_binding L x v strict) o

  | red_expr_env_record_set_mutable_binding_1_decl : forall v_old mu S C L x v (strict : bool) D o,
      decl_env_record_binds D x mu v_old ->  (* Note: spec says that there is a binding *)
      o = (If mutability_is_mutable mu
            then out_void (env_record_write_decl_env S L x mu v)
            else (if strict then (out_type_error S) else (out_void S))) ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v strict (env_record_decl D)) o

  | red_expr_env_record_set_mutable_binding_1_obj : forall S C L x v strict l pt o,
      red_expr S C (spec_object_put l x v strict) o ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v strict (env_record_object l pt)) o

  (** Auxiliary: combined create and set mutable binding *)

  | red_expr_env_record_create_set_mutable_binding : forall S C L x deletable_opt v strict o o1,
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o1 ->
      red_expr S C (spec_env_record_create_set_mutable_binding_1 o1 L x v strict) o ->
      red_expr S C (spec_env_record_create_set_mutable_binding L x deletable_opt v strict) o

  | red_expr_env_record_create_set_mutable_binding_1 : forall S S0 C L x v strict o,
      red_expr S C (spec_env_record_set_mutable_binding L x v strict) o ->
      red_expr S0 C (spec_env_record_create_set_mutable_binding_1 (out_void S) L x v strict) o

  (** Get binding *)

  | red_expr_env_record_get_binding_value : forall E S C L x strict o,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_get_binding_value_1 L x strict E) o ->
      red_expr S C (spec_env_record_get_binding_value L x strict) o

  | red_expr_env_record_get_binding_value_1_decl : forall mu v S C L x strict D o,
      decl_env_record_binds D x mu v -> (* spec says: assert there is a binding *)
      o = (If mu = mutability_uninitialized_immutable
              then (out_ref_error_or_undef S strict)
              else (out_ter S v)) ->
      red_expr S C (spec_env_record_get_binding_value_1 L x strict (env_record_decl D)) o

  | red_expr_env_record_get_binding_value_1_obj : forall o1 S C L x strict l pt o,
      red_expr S C (spec_object_has_prop l x) o1 ->
      red_expr S C (spec_env_record_get_binding_value_2 x strict l o1) o ->
      red_expr S C (spec_env_record_get_binding_value_1 L x strict (env_record_object l pt)) o

  | red_expr_env_record_get_binding_value_obj_2_true : forall S0 C x strict l S o,
      red_expr S C (spec_object_get l x) o ->
      red_expr S0 C (spec_env_record_get_binding_value_2 x strict l (out_ter S true)) o

  | red_expr_env_record_get_binding_value_2_false : forall S0 C x strict l S,
      red_expr S0 C (spec_env_record_get_binding_value_2 x strict l (out_ter S false)) (out_ref_error_or_undef S strict)

  (** Delete binding *)

  | red_expr_env_record_delete_binding : forall S C L x o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_delete_binding_1 L x E) o ->
      red_expr S C (spec_env_record_delete_binding L x) o

  | red_expr_env_record_delete_binding_1_decl_indom : forall mu v S C L x D S' b,
      decl_env_record_binds D x mu v ->
      (If (mu = mutability_deletable)
          then (S' = env_record_write S L (decl_env_record_rem D x) /\ b = true)
          else (S' = S /\ b = false))  ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl D)) (out_ter S' b)

  | red_expr_env_record_delete_binding_1_decl_not_indom : forall S C L x D,
      ~ decl_env_record_indom D x ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl D)) (out_ter S true)

  | red_expr_env_record_delete_binding_1_obj : forall S C L x l pt o,
      red_expr S C (spec_object_delete l x throw_false) o ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_object l pt)) o

  (** Record implicit this value *)

  | red_expr_env_record_implicit_this_value : forall S C L o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_implicit_this_value_1 L E) o ->
      red_expr S C (spec_env_record_implicit_this_value L) o

  | red_expr_env_record_implicit_this_value_1_decl : forall S C L D,
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_decl D)) (out_ter S undef)

  | red_expr_env_record_implicit_this_value_1_obj : forall S C L l (provide_this : bool) v,
      v = (if provide_this then (value_object l) else undef) ->
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_object l provide_this)) (out_ter S v)

  (*------------------------------------------------------------*)
  (** ** Operations on lexical environments *)

  (** Get identifier reference *)

  | red_expr_lexical_env_get_identifier_ref_nil : forall S C x strict r,
      r = ref_create_value undef x strict ->
      red_expr S C (spec_lexical_env_get_identifier_ref nil x strict) (out_ter S r)

  | red_expr_lexical_env_get_identifier_ref_cons : forall S C L lexs x strict o,
      red_expr S C (spec_lexical_env_get_identifier_ref_1 L lexs x strict) o ->
      red_expr S C (spec_lexical_env_get_identifier_ref (L::lexs) x strict) o

  | red_expr_lexical_env_get_identifier_ref_cons_1 : forall o1 S C L lexs x strict o,
      red_expr S C (spec_env_record_has_binding L x) o1 ->
      red_expr S C (spec_lexical_env_get_identifier_ref_2 L lexs x strict o1) o ->
      red_expr S C (spec_lexical_env_get_identifier_ref_1 L lexs x strict) o

  | red_expr_lexical_env_get_identifier_ref_cons_2_true : forall S0 C L lexs x strict S r,
      r = ref_create_env_loc L x strict ->
      red_expr S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x strict (out_ter S true)) (out_ter S r)

  | red_expr_lexical_env_get_identifier_ref_cons_2_false : forall S0 C L lexs x strict S o,
      red_expr S C (spec_lexical_env_get_identifier_ref lexs x strict) o ->
      red_expr S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x strict (out_ter S false)) o
      
  (** TODO : 10.4.2 Entering eval code *)    

  | red_expr_execution_ctx_eval_call : forall S C K bd o,
      red_expr S C (spec_execution_ctx_eval_call K bd) o  

  (** Function call --- TODO: check this section*)

  | red_expr_execution_ctx_function_call_direct : forall bd strict newthis S C K func this args o,
      object_code S func (Some bd) ->
      strict = function_body_is_strict bd ->
      (If (strict = true) then newthis = this
      else If this = null \/ this = undef then newthis = builtin_global
      else If type_of this = type_object then newthis = this
      else False) (* ~ function_call_should_call_to_object this strict *)
      ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args strict (out_ter S newthis)) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  | red_expr_execution_ctx_function_call_convert : forall bd strict o1 S C K func this args o,
      object_code S func (Some bd) ->
      strict = function_body_is_strict bd ->
      (~ (strict = true) /\ this <> null /\ this <> undef /\ type_of this <> type_object) ->
      red_expr S C (spec_to_object this) o1 ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args strict o1) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  | red_expr_execution_ctx_function_call_1 : forall scope bd S' lex' C' strict o1 S0 C K func args S this o,
      object_scope S func (Some scope) ->
      object_code S func (Some bd) ->
      (lex', S') = lexical_env_alloc_decl S scope ->
      C' = execution_ctx_intro_same lex' this strict ->
      red_expr S' C' (spec_execution_ctx_binding_instantiation (Some func) (body_prog bd) args) o1 ->
      red_expr S' C' (spec_execution_ctx_function_call_2 K o1) o ->
      red_expr S0 C (spec_execution_ctx_function_call_1 K func args strict (out_ter S this)) o 
      
  | red_expr_execution_ctx_function_call_2 : forall S0 S C K o,
      red_expr S C K o ->
      red_expr S0 C (spec_execution_ctx_function_call_2 K (out_void S)) o

  (** Binding instantiation --- TODO: check this section *)
  
  (* Auxiliary reductions form Binding instantiation *)
  
  (* Create bindings for formal parameters Step 4d. *)

  | red_expr_binding_instantiation_formal_params_empty : forall S C K args L o,  (* Loop ends in Step 4d *)  
      red_expr S C (K args L) o ->
      red_expr S C (spec_binding_instantiation_formal_params K args L nil) o

  | red_expr_binding_instantiation_formal_params_non_empty : forall o1 S C K args L argname names o, (* Steps 4d i - iii *)
      let v := hd undef args in
      red_expr S C (spec_env_record_has_binding L argname) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_1 K (tl args) L argname names v o1) o ->
      red_expr S C (spec_binding_instantiation_formal_params K args L (argname::names)) o

  | red_expr_binding_instantiation_formal_params_1_declared : forall S S0 C K args L argname names v o,  (* Step 4d iv *)
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L argname names v (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L argname names v (out_ter S true)) o

  | red_expr_binding_instantiation_formal_params_1_not_declared : forall o1 S S0 C K args L argname names v o, (* Step 4d iv *)
      red_expr S C (spec_env_record_create_mutable_binding L argname None) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L argname names v o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L argname names v (out_ter S false)) o

  | red_expr_binding_instantiation_formal_params_2 : forall o1 S S0 C K args L argname names v o,  (* Step 4d v *)
      red_expr S C (spec_env_record_set_mutable_binding L argname v (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_3 K args L names o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_2 K args L argname names v (out_void S)) o

  | red_expr_binding_instantiation_formal_params_3 : forall o1 S S0 C K args L names o, (* Step 4d loop *)
      red_expr S C (spec_binding_instantiation_formal_params K args L names) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_3 K args L names (out_void S)) o
      
  (* Create bindings for function declarations Step 5 *)
  
  | red_expr_spec_binding_instantiation_function_decls_nil : forall o1 L S0 S C K args bconfig o, (* Step 5b *)
      red_expr S C (K L) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L nil bconfig (out_void S)) o

  | red_expr_binding_instantiation_function_decls_cons : forall o1 L S0 S C K args fd fds bconfig o, (* Step 5b *)
      let strict := function_body_is_strict (fd_body fd) in
      red_expr S C (spec_creating_function_object (fd_parameters fd) (fd_body fd) (execution_ctx_variable_env C) strict) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_1 K args L fd fds strict bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L (fd::fds) bconfig (out_void S)) o

  | red_expr_spec_binding_instantiation_function_decls_1 : forall o1 L S0 S C K args fd fds strict fo bconfig o, (* Step 5c *)
      red_expr S C (spec_env_record_has_binding L (fd_name fd)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_2 K args L fd fds strict fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_1 K args L fd fds strict bconfig (out_ter S fo)) o

  | red_expr_spec_binding_instantiation_function_decls_2_false : forall o1 L S0 S C K args fd fds strict fo bconfig o, (* Step 5d *)
      red_expr S C (spec_env_record_create_mutable_binding L (fd_name fd) (Some bconfig)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds strict fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds strict fo bconfig (out_ter S false)) o

  | red_expr_spec_binding_instantiation_function_decls_2_true_global : forall A o1 L S0 S C K args fd fds strict fo bconfig o, (* Step 5e ii *)
      object_get_property S builtin_global (fd_name fd) (prop_descriptor_some A) ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds strict fo A (prop_attributes_configurable A) bconfig) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args env_loc_global_env_record fd fds strict fo bconfig (out_ter S true)) o

  | red_expr_spec_binding_instantiation_function_decls_3_true : forall o1 L S C K args fd fds strict fo bconfig o, (* Step 5e iii *)
      let A := prop_attributes_create_data undef true true bconfig in
      red_expr S C (spec_object_define_own_prop builtin_global (fd_name fd) A true) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds strict fo bconfig o1) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds strict fo A (Some true) bconfig) o

  | red_expr_spec_binding_instantiation_function_decls_3_false_type_error : forall o1 L S C K args fd fds strict fo A configurable bconfig o, (* Step 5e iv *)
      configurable <> Some true ->
      prop_descriptor_is_accessor A \/ (prop_attributes_writable A <> Some true \/ prop_attributes_enumerable A <> Some true) ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds strict fo A configurable bconfig) (out_type_error S)

  | red_expr_spec_binding_instantiation_function_decls_3_false : forall o1 L S C K args fd fds strict fo A configurable bconfig o, (* Step 5e iv *)
     configurable <> Some true ->
      ~ (prop_descriptor_is_accessor A) /\ prop_attributes_writable A = Some true /\ prop_attributes_enumerable A = Some true ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds strict fo bconfig (out_void S)) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds strict fo A configurable bconfig) o

  | red_expr_spec_binding_instantiation_function_decls_2_true : forall o1 L S0 S C K args fd fds strict fo bconfig o, (* Step 5e *)
      L <> env_loc_global_env_record ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds strict fo bconfig (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds strict fo bconfig (out_ter S true)) o

  | red_expr_spec_binding_instantiation_function_decls_4 : forall o1 L S0 S C K args fd fds strict fo bconfig o, (* Step 5f *)
      red_expr S C (spec_env_record_set_mutable_binding L (fd_name fd) (value_object fo) strict) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls K args L fds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_4 K args L fd fds strict fo bconfig (out_void S)) o
      
  (* Create bindings for variable declarations Step 8 *)
      
  | red_expr_spec_binding_instantiation_var_decls_non_empty : forall o1 L S0 S C vd vds bconfig o, (* Step 8b *)
      red_expr S C (spec_env_record_has_binding L vd) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls_1 L vd vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls L (vd::vds) bconfig (out_void S)) o

  | red_expr_spec_binding_instantiation_var_decls_1_true : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S true)) o

  | red_expr_spec_binding_instantiation_var_decls_1_false : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      red_expr S C (spec_env_record_create_set_mutable_binding L vd (Some bconfig) undef (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S false)) o

  | red_expr_spec_binding_instantiation_var_decls_empty : forall o1 L S0 S C bconfig o, (* Step 8 *)
      red_expr S0 C (spec_binding_instantiation_var_decls L nil bconfig (out_void S)) (out_void S)     
      
  (* Declaration Binding Instantiation Main Part *)    

  | red_expr_execution_ctx_binding_instantiation : forall L tail S C func code args o, (* Step 1 *)
      (* todo: handle eval case -- step 2 *)
      (* todo: [code] needs to contain all the function declarations and the variable declarations *)

      execution_ctx_variable_env C = L :: tail ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 func code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation func code args) o
      (* Assumption made: if func is None, then code is global code or eval code, otherwise it is function code. 
         TODO: have an enumeration code_type? *)

  | red_expr_execution_ctx_binding_instantiation_1_function : forall names_option S C func code args L o, (* Step 4a *)
      object_formal_parameters S func names_option ->
      let names := unsome_default nil names_option in
      red_expr S C (spec_binding_instantiation_formal_params (spec_execution_ctx_binding_instantiation_2 code) args L names) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 (Some func) code args L) o

  | red_expr_execution_ctx_binding_instantiation_1_not_function : forall L S C code args o, (* Step 4 *)
      red_expr S C (spec_execution_ctx_binding_instantiation_2 code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 None code args L) o

  | red_expr_execution_ctx_binding_instantiation_function_2 : forall bconfig L S C code args o, (* Step 5 *)
      bconfig = false (* TODO: configurableBindings with eval *) ->
      let fds := function_declarations code in
      red_expr S C (spec_binding_instantiation_function_decls (spec_execution_ctx_binding_instantiation_3 code bconfig) args L fds bconfig (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 code args L) o

  (* TODO steps 6-7 *)

  | red_expr_execution_ctx_binding_instantiation_3 : forall o1 L S C code bconfig o, (* Step 8 *)
      let vds := variable_declarations code in
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_3 code bconfig L) o
      
  (** Creating function object *)
    
  | red_expr_creating_function_object_proto : forall o1 S0 S C K l b o, 
      red_expr S C (spec_constructor_builtin builtin_object_new nil) o1 ->
      red_expr S C (spec_creating_function_object_proto_1 K l o1) o ->
      red_expr S0 C (spec_creating_function_object_proto K l (out_ter S b)) o
    
  | red_expr_creating_function_object_proto_1 : forall o1 S0 S C K l lproto b o, 
      let A := prop_attributes_create_data (value_object l) true false true in 
      red_expr S C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
      red_expr S C (spec_creating_function_object_proto_2 K l lproto o1) o ->
      red_expr S0 C (spec_creating_function_object_proto_1 K l (out_ter S lproto)) o
      
   | red_expr_creating_function_object_proto_2 : forall o1 S0 S C K l lproto b o, 
      let A := prop_attributes_create_data (value_object lproto) true false false in 
      red_expr S C (spec_object_define_own_prop l "prototype" A false) o1 ->
      red_expr S C (K o1) o ->
      red_expr S0 C (spec_creating_function_object_proto_2 K l lproto (out_ter S b)) o
  
  | red_expr_creating_function_object : forall l S' o1 S C names bd X strict o,
      let O := object_create builtin_function_proto "Function" true builtin_spec_op_function_get Heap.empty in
      let O1 := object_with_invokation O 
        (Some builtin_spec_op_function_constructor) 
        (Some builtin_spec_op_function_call) 
        (Some builtin_spec_op_function_has_instance) in
      let O2 := object_with_details O1 (Some X) (Some names) (Some bd) None None None None in
      (l, S') = object_alloc S O2 ->
      let A := prop_attributes_create_data (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_proto (spec_creating_function_object_1 strict l) l o1) o ->
      red_expr S C (spec_creating_function_object names bd X strict) o
                     


   | red_expr_creating_function_object_1_not_strict : forall o1 S0 S C l b, 
      red_expr S0 C (spec_creating_function_object_1 false l (out_ter S b)) (out_ter S l)
      
   | red_expr_creating_function_object_1_strict : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "caller" A false) o1 ->
      red_expr S C (spec_creating_function_object_2 l o1) o ->
      red_expr S0 C (spec_creating_function_object_1 true l (out_ter S b)) o
      
  | red_expr_creating_function_object_2 : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "arguments" A false) o1 ->
      red_expr S C (spec_creating_function_object_3 l o1) o ->
      red_expr S0 C (spec_creating_function_object_2 l (out_ter S b)) o
      
  | red_expr_creating_function_object_3 : forall o1 S0 S C l b o, 
      red_expr S0 C (spec_creating_function_object_3 l (out_ter S b)) (out_ter S l)
      
  | red_expr_spec_call_builtin: forall S C builtinid lo this args o,
      builtinid <> builtin_spec_op_function_call /\ builtinid <> builtin_spec_op_function_bind_call ->
      red_expr S C (spec_call_builtin builtinid args) o -> 
      red_expr S C (spec_call builtinid lo this args) o
      
  | red_expr_spec_call_p: forall S C l this args o,
      red_expr S C (spec_op_function_call l this args) o -> 
      red_expr S C (spec_call builtin_spec_op_function_call (Some l) (Some this) args) o
      
  | red_expr_spec_call_prog: forall S C l this args o,      
      red_expr S C (spec_execution_ctx_function_call (spec_op_function_call_1 l) l this args) o ->
      red_expr S C (spec_op_function_call l this args) o
      
  | red_expr_spec_call_prog_1_empty: forall p o1 S C l o,
      (* TODO: check if red_prog return (normal, undef, empty) if function body is empty *)
      object_code S l None ->
      red_expr S C (spec_op_function_call_1 l) (out_ter S (res_normal undef))
      
  | red_expr_spec_call_prog_1_prog: forall bd o1 S C l o,
      object_code S l (Some bd) ->
      red_prog S C (body_prog bd) o1 ->
      red_expr S C (spec_op_function_call_2 o1) o ->
      red_expr S C (spec_op_function_call_1 l) o
      
  | red_expr_spec_call_prog_2_throw: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_throw v))) (out_ter S (res_throw v))
      
  | red_expr_spec_call_prog_2_return: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_return v))) (out_ter S (res_normal v))
      
  | red_expr_spec_call_prog_2_normal: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_normal v))) (out_ter S (res_normal undef))
      
  | red_expr_spec_constructor_builtin: forall S C builtinid lo args o,
      builtinid <> builtin_spec_op_function_constructor /\ builtinid <> builtin_spec_op_function_bind_constructor ->
      red_expr S C (spec_constructor_builtin builtinid args) o -> 
      red_expr S C (spec_constructor builtinid lo args) o
      
  | red_expr_spec_constructor_function: forall S C l args o,
      red_expr S C (spec_function_constructor l args) o -> 
      red_expr S C (spec_constructor builtin_spec_op_function_constructor (Some l) args) o
      
  | red_expr_spec_function_constructor : forall o1 S C l args o,
      red_expr S C (spec_object_get (value_object l) "prototype") o1 ->
      red_expr S C (spec_function_constructor_1 l args o1) o ->
      red_expr S C (spec_function_constructor l args) o
      
  | red_expr_spec_function_constructor_1 : forall l' proto O S' builtinid o1 S0 S C l args v o,
      proto = (If (type_of v) = type_object then v
               else builtin_object_proto) ->
      O = object_create proto "Object" true builtin_spec_op_object_get Heap.empty ->
      (l', S') = object_alloc S O ->
      object_call S' l (Some builtinid) ->
      red_expr S' C (spec_call builtinid (Some l) (Some (value_object l')) args) o1 ->
      red_expr S' C (spec_function_constructor_2 l' o1) o ->
      red_expr S0 C (spec_function_constructor_1 l args (out_ter S v)) o
      
  | red_expr_spec_function_constructor_2 : forall S0 S C l' v vr o,
      vr = (If (type_of v = type_object) then v else l') ->
      red_expr S0 C (spec_function_constructor_2 l' (out_ter S v)) (out_ter S vr)
      
(*      

      
      
      let A := prop_attributes_create_data (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_proto (spec_creating_function_object_1 strict l) l o1) o ->
*)

(* TODO: spec_object_put_special *)

(*------------------------------------------------------------*)
(** ** Global object builtin functions *)

  (** IsNan *)

  | red_spec_call_global_is_nan : forall S C v o o1 args, 
      arguments_from args (v::nil)  -> 
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_global_is_nan o1) o ->
      red_expr S C (spec_call_builtin builtin_global_is_nan args) o

  | red_spec_call_global_is_nan_1 : forall S S0 C b n,
      b = (ifb n = JsNumber.nan then true else false) ->
      red_expr S0 C (spec_call_global_is_nan (out_ter S n)) (out_ter S b)

  (** IsFinite *)

  | red_spec_call_global_is_finite : forall S C v o o1 args, 
      arguments_from args (v::nil)  ->
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_global_is_finite o1) o ->
      red_expr S C (spec_call_builtin builtin_global_is_finite args) o

  | red_spec_call_global_is_finite_1 : forall S S0 C b n,
      b = (ifb n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity then false else true) ->
      red_expr S0 C (spec_call_global_is_finite (out_ter S n)) (out_ter S b)   
      
  (** 15.1.2.1 eval *)  
  
  | red_spec_call_global_eval_not_string : forall S C args v,
      arguments_from args (v::nil) ->
      type_of v <> type_string ->
      red_expr S C (spec_call_builtin builtin_global_eval args) (out_ter S v)  
      
  | red_spec_call_global_eval_string : forall v s p S C args o,
      arguments_from args (v::nil) ->
      type_of v = type_string ->
      v = prim_string s ->
      ~ (parse s p) ->
      (* TODO see also clause 16 *)
      red_expr S C (spec_error builtin_syntax_error) o -> 
      red_expr S C (spec_call_builtin builtin_global_eval args) o 
      
  | red_spec_call_global_eval_string_parse : forall v s p S C args v o,
      arguments_from args (v::nil) ->
      type_of v = type_string ->
      v = prim_string s ->
      parse s p ->
      red_expr S C (spec_execution_ctx_eval_call (spec_call_global_eval p) (body_intro p s)) o ->
      red_expr S C (spec_call_builtin builtin_global_eval args) o 
      
  | red_spec_call_global_eval : forall o1 S C p o,
      red_prog S C p o1 ->
      red_expr S C (spec_call_global_eval_1 o1) o ->
      red_expr S C (spec_call_global_eval p) o  
      
  | red_spec_call_global_eval_1_normal_value: forall S C v,
      red_expr S C (spec_call_global_eval_1 (out_ter S v)) (out_ter S v)
      
  | red_spec_call_global_eval_1_normal_empty: forall S C v,
      red_expr S C (spec_call_global_eval_1 (out_ter S (res_normal ret_or_empty_empty))) (out_ter S undef)
      
  | red_spec_call_global_eval_1_throw: forall S C v,
      red_expr S C (spec_call_global_eval_1 (out_ter S (res_throw v))) (out_ter S (res_throw v))     
     

(*------------------------------------------------------------*)
(** ** Object builtin functions *)

  (** getPrototypeOf *)
  
  | red_spec_call_object_get_prototype_of : forall S C v r args, 
      arguments_from args (v::nil) ->
      type_of v = type_object ->
      r = (ref_create_value v "prototype" false) ->
      red_expr S C (spec_call_builtin builtin_object_get_prototype_of args) (out_ter S (ret_ref r))
      
  (** new Object ([value]) 15.2.2.1. *)
  
  | red_spec_object_constructor_obj : forall v S C args,
      (* TODO: handle host objects *)
      arguments_from args (v::nil) ->
      type_of v = type_object ->
      red_expr S C (spec_constructor_builtin builtin_object_new args) (out_ter S v)
      
  | red_spec_object_constructor_prim : forall v S C args o,
      arguments_from args (v::nil) ->
      type_of v = type_string \/ type_of v = type_bool \/ type_of v = type_number ->
      red_expr S C (spec_to_object v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_new args) o
 
   | red_spec_object_constructor_nil : forall v O S' S C args l,
      arguments_from args (v::nil) ->
      type_of v = type_null \/ type_of v = type_undef ->
      O = object_create builtin_object_proto "Object" true builtin_spec_op_object_get Heap.empty ->
      (l, S') = object_alloc S O ->
      red_expr S C (spec_constructor_builtin builtin_object_new args) (out_ter S' l)
  
  
(*------------------------------------------------------------*)
(** ** Object prototype builtin functions *)

  (** Object.prototype.toString() *)

  (* Daniele: we can factorize the two rules for undef and null *)
  | red_spec_call_object_proto_to_string_undef : forall S C v v1 o args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      v = undef ->
      red_expr S C (spec_call_builtin builtin_object_proto_to_string args) (out_ter S "[object Undefined]"%string)

  | red_spec_call_object_proto_to_string_null : forall S C v v1 o args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      v = null ->
      red_expr S C (spec_call_builtin builtin_object_proto_to_string args) (out_ter S "[object Null]"%string)

  | red_spec_call_object_proto_to_string_other : forall S C v v1 o o1 args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      not (v = null \/ v = undef) ->
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (spec_call_object_proto_to_string o1) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_to_string args) o

  | red_spec_call_object_proto_to_string : forall S S0 C l s s1 o o1,
      object_class S l s1 ->
      s = "[object " ++ s1 ++ "]" ->
      red_expr S C (spec_call_object_proto_to_string (out_ter S0 l)) (out_ter S0 s)

   (** Object.prototype.isPrototypeOf() *)

   (* If the argument is not an object return false *)
   | red_spec_call_object_proto_is_prototype_of_not_object : forall S C v v1 o args w, 
      arguments_from args (v::nil)  ->
      v = value_prim w ->
      red_expr S C (spec_call_builtin builtin_object_proto_is_prototype_of args) (out_ter S false)

  (* old : replaced by the next 2 rules
  | red_spec_call_object_proto_is_prototype_of_object : forall S C v vt l o o1 sp args, 
      arguments_from args (v::nil) ->                                             
      v = value_object l ->
      vt = execution_ctx_this_binding C ->
      red_expr S C (spec_to_object vt) o1 ->
      object_proto S l sp -> (* [spec_to_object] may change the heap:  I think this should be runned on the new computed heap. -- Martin *)
      red_expr S C (spec_call_object_proto_is_prototype_of o1 sp) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_is_prototype_of args) o
  *)

  (* If the argument is an object, first get toObject(this) then move on *)
  | red_spec_call_object_proto_is_prototype_of_object : forall S C v vt l o o1 args, 
      arguments_from args (v::nil) ->                                             
      v = value_object l ->
      vt = execution_ctx_this_binding C ->  
      red_expr S C (spec_to_object vt) o1 ->
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of_1 o1 l) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_is_prototype_of args) o

  (* Now get the prototype of the argument *)
  | red_spec_call_object_proto_is_prototype_of_object_1 : forall S S' C v vt l o o1 sp,
      object_proto S l sp -> 
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of vt sp) o ->
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of_1 (out_ter S' vt) l) o

  (* Compare this and the prototype of the argument... *)
  | red_spec_call_object_proto_is_prototype_of_1_null : forall S0 S C o vt,
      red_expr S0 C (spec_call_builtin_object_proto_is_prototype_of vt null) (out_ter S false)
  
  | red_spec_call_object_proto_is_prototype_of_1_same : forall S C vt v,
      vt = v ->
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of vt v) (out_ter S true)

  | red_spec_call_object_proto_is_prototype_of_1_loop : forall S C vt v o,
      not (vt = v \/ v = null) ->
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of_1 (out_ter S vt) v) o ->
      red_expr S C (spec_call_builtin_object_proto_is_prototype_of vt v) o

  (** Object.prototype.valueOf() - [15.2.4.4] *)

  (* Daniele: - ignoring host objects for now (TODO) 
              - implementation dependent part: we always return O (as Sergio suggested)*)

  | red_spec_call_object_proto_value_of : forall S C args vt o,   
      arguments_from args nil ->                                             
      vt = execution_ctx_this_binding C ->
      red_expr S C (spec_to_object vt) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_value_of args) o 

  (*------------------------------------------------------------*)
  (** ** Boolean builtin functions *)

  (** [15.6.1]: Boolean(value) *)

  (* Just performs a type conversion [toBoolean] *)
  | red_spec_call_bool_call : forall S C v o args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_to_boolean v) o ->
      red_expr S C (spec_call_builtin builtin_bool_call args) o 

  (** [15.6.2.1]: new Boolean(value) *)
  
  | red_spec_bool_constructor : forall S C v o o1 args,
      arguments_from args (v::nil) -> 
      red_expr S C (spec_to_boolean v) o1 ->
      red_expr S C (spec_constructor_builtin_bool_new o1) o ->
      red_expr S C (spec_constructor_builtin builtin_bool_new args) o
  
   | red_spec_bool_constructor_1 : forall O l b S' S C,
      let O1 := object_create builtin_bool_proto "Boolean" true builtin_spec_op_object_get Heap.empty in 
      let O := object_with_primitive_value O1 b in 
      (l, S') = object_alloc S O ->
      red_expr S C (spec_constructor_builtin_bool_new (out_ter S b)) (out_ter S' l) 

  (*------------------------------------------------------------*)
  (** ** Boolean prototype builtin functions *)
  
  (** Boolean.prototype.toString() *)

  | red_spec_call_bool_proto_to_string_boolean : forall S C v v1 b s o args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      type_of v = type_bool ->
      red_expr S C (spec_call_builtin_bool_proto_to_string_1 v) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_to_string args) (out_ter S s)

  | red_spec_call_bool_proto_to_string_object : forall S C l v v1 o o1 sc args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      type_of v = type_object ->
      v = value_object l ->
      object_class S l sc ->
      red_expr S C (spec_call_builtin_bool_proto_to_string sc l) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_to_string args) o

  | red_spec_call_bool_proto_to_string_object_boolean : forall S C l b s o o1,
      s = "Boolean" ->
      object_prim_value S l b ->
      red_expr S C (spec_call_builtin_bool_proto_to_string_1 b) o ->
      red_expr S C (spec_call_builtin_bool_proto_to_string s l) o

   | red_spec_call_bool_proto_to_string_object_not_boolean : forall S C b v s o,
      not (s = "Boolean") ->
      red_expr S C spec_init_throw_type_error o ->
      red_expr S C (spec_call_builtin_bool_proto_to_string s b) o

  | red_spec_call_bool_proto_to_string_1 : forall S C s b, 
      s = (if decide (b = true) then "true" else "false") ->
      red_expr S C (spec_call_builtin_bool_proto_to_string_1 b) (out_ter S s)

   (** Boolean.prototype.valueOf() *)

   (* Daniele: it is really the same thing as the previous one ([Boolean.prototype.toString()]), 
      with the only difference that at the ends it returns the real value instead of its string
      representation. Should be factorized? I just copied and pasted and fixed one line (see comment below). *)

  | red_spec_call_bool_proto_value_of_boolean : forall S C v v1 b s o args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      type_of v = type_bool ->
      red_expr S C (spec_call_builtin_bool_proto_value_of_1 v) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of args) (out_ter S s)

  | red_spec_call_bool_proto_value_of_object : forall S C l v v1 o o1 sc args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      type_of v = type_object ->
      v = value_object l ->
      object_class S l sc ->
      red_expr S C (spec_call_builtin_bool_proto_value_of sc l) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of args) o

  | red_spec_call_bool_proto_value_of_object_boolean : forall S C l b s o o1,
      s = "Boolean" ->
      object_prim_value S l b ->
      red_expr S C (spec_call_builtin_bool_proto_value_of_1 b) o ->
      red_expr S C (spec_call_builtin_bool_proto_value_of s l) o

   | red_spec_call_bool_proto_value_of_object_not_boolean : forall S C b v s o,
      not (s = "Boolean") ->
      red_expr S C spec_init_throw_type_error o ->
      red_expr S C (spec_call_builtin_bool_proto_value_of s b) o

  (* Daniele: This rule is the only difference between [Boolean.prototype.valueOf()]
     and [Boolean.prototype.toString()] *)
  | red_spec_call_bool_proto_value_of_1 : forall S C s b, 
      red_expr S C (spec_call_builtin_bool_proto_value_of_1 b) (out_ter S b)

  (*------------------------------------------------------------*)
  (** ** Number builtin functions *)

  (** [15.7.1.1]: Number(value) *)

  (* Just performs a type conversion [toNumber] *)
  | red_spec_call_number_call : forall S C v o args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_to_number v) o ->
      red_expr S C (spec_call_builtin builtin_number_call args) o

  (** [15.7.2.1]: new Number([value]) *)
  
  (* Daniele: do I have to type [(value_prim (prim_number (JsNumber.of_int k)))] 
     every time? Shortcuts? *)

  (* If [value] is not supplied, the default value is 0 *)
  | red_spec_number_constructor_no_value : forall S C o o1 args,
      arguments_from args nil -> 
      o1 = (out_ter S (value_prim (prim_number (JsNumber.of_int 10)))) ->
      red_expr S C (spec_constructor_builtin_number_new o1) o ->
      red_expr S C (spec_constructor_builtin builtin_number_new args) o

  (* If [value] is supplied, we call toNumber(value) and move on *)
  | red_spec_number_constructor_value : forall S C v o o1 args,
      arguments_from args (v::nil) -> 
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_constructor_builtin_number_new o1) o ->
      red_expr S C (spec_constructor_builtin builtin_number_new args) o
  
  (* We create the new object using the provided value (or the default one, zero) *)
  | red_spec_number_constructor_1 : forall O l v S' S C,
      let O1 := object_create builtin_number_proto "Number" true builtin_spec_op_object_get Heap.empty in
      let O := object_with_primitive_value O1 v in 
      (l, S') = object_alloc S O ->
      red_expr S C (spec_constructor_builtin_number_new (out_ter S v)) (out_ter S' l) 

  (*------------------------------------------------------------*)
  (** ** Number prototype builtin functions *)

  (* 15.7.4.2: Number.prototype.toString([radix]) *)

  (* Daniele: I guess we don't have the algorithm for representing numbers 
     as strings with different radix. I'll just ignore this (i.e. always do
     toString in base 10) *)

  (* Daniele: I'm not convinced by this one :/ *)
  
  (* if [this] is not a number then throw Type Error exception *)
  | red_spec_call_number_proto_to_string_not_number : forall S C s b o v args, 
      v = execution_ctx_this_binding C ->
      not (type_of v = type_number) -> (* Daniele: check last lines of [15.7.4.2]. *)
      red_expr S C spec_init_throw_type_error o ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string args) o

  (* if [this] is a number we proceed to the next stages *)
  | red_spec_call_number_proto_to_string_number : forall S C s b o v args, 
      v = execution_ctx_this_binding C ->
      type_of v = type_number -> 
      red_expr S C (spec_call_builtin_number_proto_to_string v args) o ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string args) o

  (* The [radix] parameter is not there: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_no_radix : forall S C v o args, 
      args = nil ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
      red_expr S C (spec_call_builtin_number_proto_to_string v args) o 

  (* The [radix] parameter is undefined: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_undef_radix : forall S C v vr args o, 
      arguments_from args (vr::nil) ->
      vr = undef ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
      red_expr S C (spec_call_builtin_number_proto_to_string v args) o 

  (* TODO: factorize the previous 2? *)

  (* The [radix] is present *)
  | red_spec_call_number_proto_to_string_number_radix : forall S C v vr args o o1,
      arguments_from args (vr::nil) ->
      not (vr = undef) ->
      red_expr S C (spec_to_integer vr) o1 ->
      red_expr S C (spec_call_builtin_number_proto_to_string_1 v o1) o -> 
      red_expr S C (spec_call_builtin_number_proto_to_string v args) o 
 
  (* If the [radix] is 10 we do a simple toString *)
  | red_spec_call_number_proto_to_string_1_radix_10 :forall S S' C v vr o,
      vr = value_prim (prim_number (JsNumber.of_int 10)) -> 
      red_expr S C (spec_to_string v) o ->
      red_expr S C (spec_call_builtin_number_proto_to_string_1 v (out_ter S' vr)) o
      
  (* If the [radix] is out of range we throw a Range Error exception *)
  | red_spec_call_number_proto_to_string_1_radix_out_of_range : forall S S' C v vr k o,
      vr = value_prim (prim_number (JsNumber.of_int k)) ->
      (k < 2 /\ k > 36) -> 
      red_expr S C spec_init_throw_type_error o -> (* Should be Range Error instead of Type Error *)
      red_expr S C (spec_call_builtin_number_proto_to_string_1 v (out_ter S' vr)) o
  
  (* If the [radix] is in range we do a simple toString 
     TODO: in fact the number should be printed using that radix
     implementation dependent) *)
  | red_spec_call_number_proto_to_string_1_radix_in_range : forall S S' C v vr k o,
      vr = value_prim (prim_number (JsNumber.of_int k)) ->
      not (k < 2 /\ k > 36) -> 
      red_expr S C (spec_to_string v) o -> (* This should be something different *)
      red_expr S C (spec_call_builtin_number_proto_to_string_1 v (out_ter S' vr)) o


  (* 15.7.4.4: Number.prototype.valueOf() *)

  (* it throws a TypeError exception if its this value is not a Number or a Number object. *)
  | red_spec_call_number_proto_value_of_not_number : forall S C v o args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      not (type_of v = type_number) -> (* ? *)
      red_expr S C spec_init_throw_type_error o ->
      red_expr S C (spec_call_builtin builtin_number_proto_value_of args) o

  (* Otherwise it returns the Number value itself *)
  | red_spec_call_number_proto_value_of_number : forall S C v args, 
      arguments_from args nil  ->
      v = execution_ctx_this_binding C ->
      type_of v = type_number ->
      red_expr S C (spec_call_builtin builtin_number_proto_value_of args) (out_ter S v)


  (** Throw Type Error Function Object Initialisation *)           
  
  (* Could we have this not a a reduction, but as simple function in JsInit? *)
  | red_spec_init_throw_type_error : forall O O1 code O2 S' A o1 S C o,
      O = object_create builtin_function_proto "Function" true builtin_spec_op_function_get Heap.empty ->
      O1 = object_with_invokation O None (Some builtin_spec_op_function_call) None ->
      (* TODO : Is this ok? *)
      code = body_intro (prog_stat (stat_throw (expr_new (expr_variable "TypeError") nil))) "throw TypeError()" -> 
      O2 = object_with_details O1 (Some (env_loc_global_env_record::nil)) (Some nil) (Some code) None None None None ->
      S' = object_write S builtin_function_throw_type_error O2 ->
      A = prop_attributes_create_data JsNumber.zero false false false ->
      red_expr S' C (spec_object_define_own_prop builtin_function_throw_type_error "length" A false) o1 ->
      red_expr S C (spec_init_throw_type_error_1 o1) o ->
      red_expr S C spec_init_throw_type_error o
  
  | red_spec_init_throw_type_error_1 : forall O S' S0 S C v o,
      object_binds S builtin_function_throw_type_error O ->
      S' = object_write S builtin_function_throw_type_error (object_set_extensible_false O) ->
      red_expr S0 C (spec_init_throw_type_error_1 (out_ter S v)) (out_void S')

  (** Auxiliary: creates a new object, then pass its address [l] 
      to a continuation [K]. Used for Object Initialiser expression. *)
  | red_spec_new_object : forall S C o o1 K, 
      red_expr S C (spec_constructor_builtin builtin_object_new nil) o1 ->
      red_expr S C (spec_new_object_1 o1 K) o ->
      red_expr S C (spec_new_object K) o

  | red_spec_new_object_1 : forall S S0 C l K o, 
      red_expr S C (K l) o ->
      red_expr S C (spec_new_object_1 (out_ter S0 l) K) o
  
  (** Shortcut: creates a new function object in the given execution context *)
  (* Daniele: [spec_creating_function_object] requires the function body as
     a string as the 2nd argument, but we don't have it. *)
  | red_spec_create_new_function_in : forall S C args bd o,
      red_expr S C (spec_creating_function_object args bd (execution_ctx_lexical_env C) (execution_ctx_strict C)) o ->
      red_expr S C (spec_create_new_function_in C args bd) o
.

(*--------------------------------*)
(* deprecated, but to keep around for wf invariants:

  | red_expr_delete_1_ref_unresolvable : forall S0 S C r o,
      ref_is_unresolvable r ->
      red_expr S C (spec_error_or_cst (ref_strict r) builtin_syntax_error true) o -> 
      red_expr S0 C (expr_delete_1 (out_ter S (ret_ref r))) o

  | red_expr_delete_3_strict : forall S C r L o,
      red_expr S C (spec_error builtin_syntax_error) o -> 
      red_expr S C (expr_delete_3 r L true) o 

  | red_expr_prepost_1_invalid : forall S0 S C op R,
      ~ valid_lhs_for_assign R ->
      red_expr S0 C (expr_prepost_1 op (out_ter S R)) (out_syntax_error S)

  | red_expr_prepost_1_valid : forall S0 S C R op o1 o,
      valid_lhs_for_assign R ->
*)
