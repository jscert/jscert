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

  | red_stat_var_decl_none : forall S C x,
      red_stat S C (stat_var_decl x None) (out_ter S undef)

    (* TODO: red_stat_var_decl_some: can we justify that this is equivalent to the spec ?*)
  | red_stat_var_decl_some : forall S C x e o1 o,
      red_expr S C (expr_assign (expr_variable x) None e) o1 ->
      red_stat S C (stat_var_decl_1 o1) o ->
      red_stat S C (stat_var_decl x (Some e)) o

  | red_stat_var_decl_1 : forall S0 S r1 C,
      red_stat S0 C (stat_var_decl_1 (out_ter S r1)) (out_ter S undef)

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
  
  | red_stat_for_in : forall o1 S C e1 e2 t o,
      red_expr S C e2 o1 ->
      red_stat S C (stat_for_in_1 e1 t o1) o ->
      red_stat S C (stat_for_in e1 e2 t) o
      
  | red_stat_for_in_1 : forall o1 S0 S C e1 t R o,
      red_expr S C (spec_get_value R) o1 ->
      red_stat S C (stat_for_in_2 e1 t o1) o ->
      red_stat S0 C (stat_for_in_1 e1 t (out_ter S R)) o
   (* todo: use spec_expr_get_value to factorize first two rules *)

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

  | red_stat_for_in_1 : forall o1 S C e1 e2 t o,
      red_expr S C e2 o1 ->
      red_stat S C (stat_for_in_1 e1 t o1) o ->
      red_stat S C (stat_for_in e1 e2 t) o

  | red_stat_for_in_2 : forall o1 S0 S C e1 t exprRef o,
      red_expr S C (spec_get_value exprRef) o1 ->
      red_stat S C (stat_for_in_2 e1 t o1) o ->
      red_stat S0 C (stat_for_in_1 e1 t (out_ter S exprRef)) o

  | red_stat_for_in_3_null_undef : forall S0 S C e1 t exprValue o,
      exprValue = null \/ exprValue = undef ->
      red_stat S0 C (stat_for_in_2 e1 t (out_ter S exprValue)) (out_void S)

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

  (** TODO:  Rules for the return,  break and continue statements *)

 (** Throw statement *)

  | red_stat_throw : forall S C e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_throw_1 o1) o ->
      red_stat S C (stat_throw e) o

  | red_stat_throw_1 : forall S0 S C v,
      red_stat S0 C (stat_throw_1 (out_ter S v)) (out_ter S (res_throw v))

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

(*---begin to clean ---*)

  (*----- TOCLEAN---

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

  (** Function declaration [TODO] *)

  (*| red_expr_function_unnamed : forall l l' S0 S1 S2 C lx P,
      object_fresh S0 l ->
      S1 = alloc_obj S0 l loc_obj_proto ->
      object_fresh S1 l' ->
      S2 = alloc_fun S1 l' s lx P l ->
      red_expr S0 C (expr_function None lx P) (out_ter S2 l') *)

  (*| red_expr_function_named : forall l l' l1 S0 S1 S2 S3 S4 C y lx P,
      object_fresh S0 l ->
      S1 = alloc_obj S0 l loc_obj_proto ->
      object_fresh S1 l1 ->
      S2 = alloc_obj S1 l1 loc_obj_proto ->
      object_fresh S2 l' ->
      S3 = alloc_fun S2 l' (l1::s) lx P l ->
      S4 = write S3 l1 (field_normal y) (value_loc l') ->
      red_expr S0 C (expr_function (Some y) lx P) (out_ter S4 l') *)

  (** Access *)

  | red_expr_access : forall S0 C e1 e2 o o1,
      red_expr S0 C e1 o1 ->
      red_expr S0 C (expr_access_1 o1 e2) o ->
      red_expr S0 C (expr_access e1 e2) o

  (*| red_expr_access_1 : forall S0 S1 C o o2 e2 v1 r l,
      getvalue S1 r v1 ->
      red_expr S1 C e2 o2 ->
      red_expr S1 C (expr_access_2 v1 o2) o ->
      red_expr S0 C (expr_access_1 (out_ter S1 r) e2) o*)

  (*| red_expr_access_2 : forall S0 S1 C r v1 v2 o,
      getvalue S1 r v2 ->
      red_expr S1 C (spec_convert_twice (spec_to_object v1) (spec_to_string v2) expr_access_3) o ->
      red_expr S0 C (expr_access_2 v1 (out_ter S1 r)) o*)

  (*| red_expr_ext_expr_access_3 :
     v1 = value_loc l ->  (* todo: generalize when references can take value as first argument *)
     x = convert_prim_to_string v2 ->
     red_expr S C (expr_access_3 v1 v2) (out_ter S (Ref l x))*)

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


  (** Call *)

(*
  | red_expr_call : forall S0 C e1 e2s o1 o2,
      red_expr S0 C (expr_basic e1) o1 ->
      red_expr S0 C (expr_call_1 o1 e2s) o2 ->
      red_expr S0 C (expr_call e1 e2s) o2
*)
  (*| red_expr_call_1 : forall S0 S1 C l1 l2 o r1 e2s,
      getvalue S1 r1 l1 ->
      l2 = get_this S1 r1 ->
      red_expr S1 C (expr_call_2 l1 l2 e2s) o ->
      red_expr S0 C (expr_call_1 (out_ter S1 r1) e2s) o*)

  (*| red_expr_call_2 : forall S0 C l1 l2 s3 P3 xs e2s o,
      l1 <> loc_eval ->
      binds S0 l1 field_scope (value_scope s3) ->
      binds S0 l1 field_body (value_body xs P3) ->
      red_expr S0 C (expr_list_then (expr_call_3 l2 (normal_body s3 xs P3)) e2s) o ->
      red_expr S0 C (expr_call_2 l1 l2 e2s) o*)

  | red_expr_call_2_eval : forall S0 C e2s l2 o,
      red_expr S0 C (expr_list_then (expr_call_3 l2 primitive_eval) e2s) o ->
      red_expr S0 C (expr_call_2 loc_eval l2 e2s) o

  (*| red_expr_call_3 : forall S0 S1 S2 S3 S4 l0 l1 o3 o ys vs xs fvs C s3 P3,
      ys = defs_prog xs P3 ->
      object_fresh S0 l1 ->
      S1 = alloc_obj S0 l1 loc_null ->
      S2 = write S1 l1 field_this l0 ->
      arguments xs vs fvs ->
      S3 = write_fields S2 l1 fvs ->
      S4 = reserve_local_vars S3 l1 ys ->
      red_expr S4 (l1::s3) (ext_expr_prog P3) o3 ->
      red_expr S4 C (expr_call_4 o3) o ->
      red_expr S0 C (expr_call_3 l0 (normal_body s3 xs P3) vs) o*)

  (*| red_expr_call_3_eval : forall S0 C vs g e3 l0 o o3,
      parse g e3 ->
      red_expr S0 C e3 o3 ->
      red_expr S0 C (expr_call_4 o3) o ->
      red_expr S0 C (expr_call_3 l0 primitive_eval (g::vs)) o*)

  (*| red_expr_call_4 : forall S0 S1 C r v,
      getvalue S1 r v ->
      red_expr S0 C (expr_call_4 (out_ter S1 r)) (out_ter S1 v)*)

---end to clean ---*)

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
      (* TODO: fix this line s = string_concat s1 s2 ->*)
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
      object_has_instance S l false ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_binary_op_3 binary_op_in v1 (value_object l)) o

  | red_expr_binary_op_instanceof_normal : forall S C v1 l o,
      object_has_instance S l true ->
      red_expr S C (spec_has_instance l v1) o ->
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
      red_expr S C (expr_binary_op_3 binary_op_strict_equal v1 v2) o

  | red_expr_binary_op_disequal : forall S C v1 v2 o1 o,
      red_expr S C (spec_equal v1 v2) o1 ->
      red_expr S C (expr_binary_op_strict_disequal_1 o1) o ->
      red_expr S C (expr_binary_op_3 binary_op_strict_disequal v1 v2) o

  | red_expr_binary_op_disequal_1 : forall S0 S C b,
      red_expr S0 C (expr_binary_op_strict_disequal_1 (out_ter S b)) (out_ter S (negb b))

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

  | red_spec_to_default_sub_2_callable : forall S C l lf K o fc o1,
      callable S lf (Some fc) ->
      red_expr S C (spec_call fc (Some lf) nil) o1 ->
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

  | red_expr_object_get : forall An S C l x o,
      object_get_property S (value_object l) x An ->
      red_expr S C (spec_object_get_1 l An) o ->
      red_expr S C (spec_object_get l x) o

  | red_expr_object_get_1_undef : forall S C l,
      red_expr S C (spec_object_get_1 l prop_descriptor_undef) (out_ter S undef)

  | red_expr_object_get_1_some_data : forall S C l A v,
      prop_attributes_is_data A ->
      prop_attributes_value A = Some v ->
      red_expr S C (spec_object_get_1 l (prop_descriptor_some A)) (out_ter S v)

  | red_expr_object_get_1_some_accessor : forall S C l A o,
      prop_attributes_is_accessor A ->
      red_expr S C (spec_object_get_2 l (prop_attributes_get A)) o ->
      red_expr S C (spec_object_get_1 l (prop_descriptor_some A)) o

  | red_expr_object_get_2_undef : forall S C l,
      red_expr S C (spec_object_get_2 l (Some undef)) (out_ter S undef)

  | red_expr_object_get_2_getter : forall fc S C l f o,
      object_call S f (Some fc) ->
      red_expr S C (spec_call fc (Some (value_object l)) nil) o ->
      red_expr S C (spec_object_get_2 l (Some (value_object f))) o

      (* TODO: what should we do for [spec_object_get_2 l None] ? *)

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
      prop_attributes_is_data AnOwn ->
      A' = prop_attributes_create_value v ->
      red_expr S C (spec_object_define_own_prop l x A' throw) o ->
      red_expr S C (spec_object_put_2 l x v throw AnOwn) o

  | red_expr_object_put_2_not_data : forall AnOwn An S C l x v throw o,
      ~ prop_attributes_is_data AnOwn ->
      object_get_property S (value_object l) x An ->
      red_expr S C (spec_object_put_3 l x v throw An) o ->
      red_expr S C (spec_object_put_2 l x v throw AnOwn) o

  | red_expr_object_put_3_accessor : forall fsetter fsettero fc S C l x v throw A o,
      prop_attributes_is_accessor A ->
      Some fsetter = prop_attributes_set A ->
      (* optional thanks to the canput test: fsetter <> undef --- Arthur: I don't understand... *)
      fsetter = value_object fsettero ->
      object_call S fsettero (Some fc) ->
      red_expr S C (spec_call fc (Some (value_object l)) (v::nil)) o ->
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
      red_expr S C e o1 ->
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
      red_expr S C (spec_env_record_set_binding_value L (ref_name r) vnew (ref_strict r)) o ->
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

  | red_expr_env_record_create_immutable_binding : forall D S C L x h',
      env_record_binds S L (env_record_decl D) -> (* Note: the spec asserts that there is a binding *)
      ~ decl_env_record_indom D x ->
      h' = env_record_write_decl_env S L x mutability_uninitialized_immutable undef ->
      red_expr S C (spec_env_record_create_immutable_binding L x) (out_void h')

  (** Initialize immutable binding *)

  | red_expr_env_record_initialize_immutable_binding : forall D v_old S C L x v h',
      env_record_binds S L (env_record_decl D) ->
      decl_env_record_binds D x mutability_uninitialized_immutable v_old -> (* Note: v_old is always undef *)
      h' = env_record_write_decl_env S L x mutability_immutable v ->
      red_expr S C (spec_env_record_initialize_immutable_binding L x v) (out_void h')

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

  | red_expr_env_record_implicit_this_value : forall S C L x o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_implicit_this_value_1 L x E) o ->
      red_expr S C (spec_env_record_implicit_this_value L x) o

  | red_expr_env_record_implicit_this_value_1_decl : forall S C L x D,
      red_expr S C (spec_env_record_implicit_this_value_1 L x (env_record_decl D)) (out_ter S undef)

  | red_expr_env_record_implicit_this_value_1_obj : forall S C L x l (provide_this : bool) v,
      v = (if provide_this then (value_object l) else undef) ->
      red_expr S C (spec_env_record_implicit_this_value_1 L x (env_record_object l provide_this)) (out_ter S v)

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

  (** Function call --- TODO: check this section*)

  | red_expr_execution_ctx_function_call_direct : forall strict newthis S C K func this args o,
      (If (strict = true) then newthis = this
      else If this = null \/ this = undef then newthis = builtin_global
      else If type_of this = type_object then newthis = this
      else False) (* ~ function_call_should_call_to_object this strict *)
      ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args (out_ter S newthis)) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  | red_expr_execution_ctx_function_call_convert : forall strict o1 S C K func this args o,
      (~ (strict = true) /\ this <> null /\ this <> undef /\ type_of this <> type_object) ->
      red_expr S C (spec_to_object this) o1 ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args o1) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  (*| red_expr_execution_ctx_function_call_1 : forall h' lex' c' strict' S0 C K func args S this o,
      (lex',h') = lexical_env_alloc_decl S (function_scope func) ->
      strict' = (function_code_is_strict (function_code func) || execution_ctx_strict C) ->
        (* todo this line may change; note that in the spec this is in done in binding instantiation *)
      c' = execution_ctx_intro_same lex' this strict' ->
      red_expr h' c' (spec_execution_ctx_binding_instantiation K func (function_code func) args) o ->
      red_expr S0 C (spec_execution_ctx_function_call_1 K func args (out_ter S this)) o *)

  (** Binding instantiation --- TODO: check this section *)

  | red_expr_execution_ctx_binding_instantiation : forall L tail S C K func code args o, (* Step 1 *)
      (* todo: handle eval case -- step 2 *)
      (* todo: [func] needs to contain all the function declarations and the variable declarations *)

      (* --> need an extended form for:  4.d. entry point, with argument "args" (a list that decreases at every loop) *)
      (* todo: step 5b ? *)
      execution_ctx_variable_env C = L :: tail ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 K func code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation K func code args) o

  | red_expr_execution_ctx_binding_instantiation_function : forall names_option S C K func code args L o, (* Step 4a *)
      object_formal_parameters S func names_option ->
      let names := unsome_default nil names_option in
      red_expr S C (spec_execution_ctx_binding_instantiation_2 K func code args L names) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 K (Some func) code args L) o
      
      (* todo: isolate substeps of (d) into a different group of rules, with more precise name *)
  | red_expr_execution_ctx_binding_instantiation_function_names_empty : forall S C K func code args L o,  (* Loop ends in Step 4d *)  
      red_expr S C (spec_execution_ctx_binding_instantiation_6 K (Some func) code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 K func code args L nil) o

  | red_expr_execution_ctx_binding_instantiation_function_names_non_empty : forall o1 S C K func code args L argname names o, (* Steps 4d i - iii *)
      let v := hd undef args in
      red_expr S C (spec_env_record_has_binding L argname) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_3 K func code (tl args) L argname names v o1) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 K func code args L (argname::names)) o

  | red_expr_execution_ctx_binding_instantiation_function_names_declared : forall S S0 C K func code args L argname names v o,  (* Step 4d iv *)
      red_expr S C (spec_execution_ctx_binding_instantiation_4 K func code args L argname names v (out_void S)) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_3 K func code args L argname names v (out_ter S true)) o

  | red_expr_execution_ctx_binding_instantiation_function_names_not_declared : forall o1 S S0 C K func code args L argname names v o, (* Step 4d iv *)
      red_expr S C (spec_env_record_create_mutable_binding L argname None) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_4 K func code args L argname names v o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_3 K func code args L argname names v (out_ter S false)) o

  | red_expr_execution_ctx_binding_instantiation_function_names_set : forall o1 S S0 C K func code args L argname names v o,  (* Step 4d v *)
      red_expr S C (spec_env_record_set_mutable_binding L argname v (function_code_strict code)) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_5 K func code args L names o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_4 K func code args L argname names v (out_void S)) o

  | red_expr_execution_ctx_binding_instantiation_function_names_loop : forall o1 S S0 C K func code args L names o, (* Step 4d loop *)
      red_expr S C (spec_execution_ctx_binding_instantiation_2 K func code args L names) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_5 K func code args L names (out_void S)) o

  | red_expr_execution_ctx_binding_instantiation_not_function : forall L S C K code args o, (* Step 4 *)
      red_expr S C (spec_execution_ctx_binding_instantiation_6 K None code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 K None code args L) o

  | red_expr_execution_ctx_binding_instantiation_function_decls : forall L S C K func code args o, (* Step 5 *)
      let fds := function_declarations code in
      red_expr S C (spec_execution_ctx_binding_instantiation_7 K func code args L fds (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_6 K func code args L) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_nil : forall o1 L S0 S C K func code args o, (* Step 5b *)
      red_expr S C (spec_execution_ctx_binding_instantiation_12 K func code args L) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_7 K func code args L nil (out_void S)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_cons : forall o1 L S0 S C K func code args fd fds o, (* Step 5b *)
      let p := fd_code fd in
      let strict := (function_code_strict code) || (function_body_is_strict p) in
      let f_code := function_code_code (fd_code fd) in
      red_expr S C (spec_creating_function_object (fd_parameters fd) (f_code) (execution_ctx_variable_env C) strict) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_8 K func code args L fd fds strict o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_7 K func code args L (fd::fds) (out_void S)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_cons_has_bindings : forall o1 L S0 S C K func code args fd fds strict fo o, (* Step 5c *)
      red_expr S C (spec_env_record_has_binding L (fd_name fd)) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_9 K func code args L fd fds strict fo o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_8 K func code args L fd fds strict (out_ter S fo)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5d : forall o1 L S0 S C K func code args fd fds strict fo o, (* Step 5d *)
      red_expr S C (spec_env_record_create_mutable_binding L (fd_name fd) (Some false)) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_11 K func code args L fd fds strict fo o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_9 K func code args L fd fds strict fo (out_ter S false)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5eii : forall A o1 L S0 S C K func code args fd fds strict fo o, (* Step 5e ii *)
      object_get_property S builtin_global (fd_name fd) (prop_descriptor_some A) ->
      red_expr S C (spec_execution_ctx_binding_instantiation_10 K func code args fd fds strict fo A (prop_attributes_configurable A)) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_9 K func code args env_loc_global_env_record fd fds strict fo (out_ter S true)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5eiii : forall o1 L S C K func code args fd fds strict fo o, (* Step 5e iii *)
      let A := prop_attributes_create_data undef true true false in (* todo: fix configurable *)
      red_expr S C (spec_object_define_own_prop builtin_global (fd_name fd) A true) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_11 K func code args env_loc_global_env_record fd fds strict fo o1) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_10 K func code args fd fds strict fo A (Some true)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5eiv_type_error : forall o1 L S C K func code args fd fds strict fo A configurable o, (* Step 5e iv *)
      configurable <> Some true ->
      prop_descriptor_is_accessor A \/ (prop_attributes_writable A <> Some true \/ prop_attributes_enumerable A <> Some true) ->
      red_expr S C (spec_execution_ctx_binding_instantiation_10 K func code args fd fds strict fo A configurable) (out_type_error S)

  | red_expr_execution_ctx_binding_instantiation_function_decls_5eiv : forall o1 L S C K func code args fd fds strict fo A configurable o, (* Step 5e iv *)
     configurable <> Some true ->
      ~ (prop_descriptor_is_accessor A) /\ prop_attributes_writable A = Some true /\ prop_attributes_enumerable A = Some true ->
      red_expr S C (spec_execution_ctx_binding_instantiation_11 K func code args env_loc_global_env_record fd fds strict fo (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_10 K func code args fd fds strict fo A configurable) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5e_false : forall o1 L S0 S C K func code args fd fds strict fo o, (* Step 5e *)
      L <> env_loc_global_env_record ->
      red_expr S C (spec_execution_ctx_binding_instantiation_11 K func code args L fd fds strict fo (out_void S)) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_9 K func code args L fd fds strict fo (out_ter S true)) o

  | red_expr_execution_ctx_binding_instantiation_function_decls_5f : forall o1 L S0 S C K func code args fd fds strict fo o, (* Step 5f *)
      red_expr S C (spec_env_record_set_mutable_binding L (fd_name fd) (value_object fo) strict) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_7 K func code args L fds o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_11 K func code args L fd fds strict fo (out_void S)) o

  (* TODO steps 6-7 *)

  | red_expr_execution_ctx_binding_instantiation_8 : forall o1 L S C K func code args o, (* Step 8 *)
      let vds := variable_declarations code in
      red_expr S C (spec_execution_ctx_binding_instantiation_13 K func code args L vds (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_12 K func code args L) o

  | red_expr_execution_ctx_binding_instantiation_8b : forall o1 L S0 S C K func code args vd vds o, (* Step 8b *)
      red_expr S C (spec_env_record_has_binding L vd) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_14 K func code args L vd vds o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_13 K func code args L (vd::vds) (out_void S)) o

  | red_expr_execution_ctx_binding_instantiation_8c_true : forall o1 L S0 S C K func code args vd vds o, (* Step 8c *)
      red_expr S C (spec_execution_ctx_binding_instantiation_13 K func code args L vds (out_void S)) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_14 K func code args L vd vds (out_ter S true)) o

  | red_expr_execution_ctx_binding_instantiation_8c_false : forall o1 L S0 S C K func code args vd vds o, (* Step 8c *)
      red_expr S C (spec_env_record_create_set_mutable_binding L vd (Some false) undef (function_code_strict code)) o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_13 K func code args L vds o1) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_14 K func code args L vd vds (out_ter S false)) o

  | red_expr_execution_ctx_binding_instantiation_8_nil : forall o1 L S0 S C K func code args o, (* Step 8 *)
      red_expr S0 C (spec_execution_ctx_binding_instantiation_13 K func code args L nil (out_void S)) (out_void S)
  
  | red_expr_creating_function_object : forall l S' o1 S C names fc X strict o,
      (* TODO: formalize Function prototype object as in 15.3.3.1 *)
      let O := object_create builtin_function_proto "Function" true Heap.empty in
      let O1 := object_with_details O (Some X) (Some names) (Some fc) None None None None in
      (* TODO: create internals for [[Get]] [[Call]] [[Construct]] [[HasInstance]] *)
      (l, S') = object_alloc S O1 ->
      let A := prop_attributes_create_data (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_1 strict l o1) o ->
      red_expr S C (spec_creating_function_object names fc X strict) o
     
  | red_expr_creating_function_object_1 : forall o1 S0 S C strict l b o, 
      red_expr S C (spec_builtin_object_new None) o1 ->
      red_expr S C (spec_creating_function_object_2 strict l o1) o ->
      red_expr S0 C (spec_creating_function_object_1 strict l (out_ter S b)) o
    
  | red_expr_creating_function_object_2 : forall o1 S0 S C strict l lproto b o, 
      let A := prop_attributes_create_data (value_object l) true false true in 
      red_expr S C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
      red_expr S C (spec_creating_function_object_3 strict l lproto o1) o ->
      red_expr S0 C (spec_creating_function_object_2 strict l (out_ter S lproto)) o
      
   | red_expr_creating_function_object_3 : forall o1 S0 S C strict l lproto b o, 
      let A := prop_attributes_create_data (value_object lproto) true false false in 
      red_expr S C (spec_object_define_own_prop l "prototype" A false) o1 ->
      red_expr S C (spec_creating_function_object_4 strict l o1) o ->
      red_expr S0 C (spec_creating_function_object_3 strict l lproto (out_ter S b)) o
      
   | red_expr_creating_function_object_4_not_strict : forall o1 S0 S C l b, 
      red_expr S0 C (spec_creating_function_object_4 false l (out_ter S b)) (out_ter S l)
      
   | red_expr_creating_function_object_4_strict : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "caller" A false) o1 ->
      red_expr S C (spec_creating_function_object_5 l o1) o ->
      red_expr S0 C (spec_creating_function_object_4 true l (out_ter S b)) o
      
  | red_expr_creating_function_object_5 : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "arguments" A false) o1 ->
      red_expr S C (spec_creating_function_object_6 l o1) o ->
      red_expr S0 C (spec_creating_function_object_5 l (out_ter S b)) o
      
  | red_expr_creating_function_object_6 : forall o1 S0 S C l b o, 
      red_expr S0 C (spec_creating_function_object_6 l (out_ter S b)) (out_ter S l)
      
  | red_expr_spec_call_builtin: forall S C builtinid args o,
      red_expr S C (spec_call_builtin builtinid args) o -> 
      red_expr S C (spec_call (function_code_builtin builtinid) None args) o
      
  | red_expr_spec_call_prog: forall S C p this args o,
      red_expr S C (spec_call_prog p this args) o -> 
      red_expr S C (spec_call (function_code_code p) (Some this) args) o
.

(* TODO: spec_object_put_special *)









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
