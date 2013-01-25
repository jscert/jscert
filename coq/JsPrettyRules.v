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
Implicit Type B : builtin.
Implicit Type T : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
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


(**************************************************************)
(** ** Reduction rules for programs (14) *)

Inductive red_prog : state -> execution_ctx -> ext_prog -> out -> Prop :=

  (** Abort rule for programs *)

  | red_prog_abort : forall S C extp o,
      out_of_ext_prog extp = Some o ->
      abort o ->
      ~ abort_intercepted_prog extp ->
      red_prog S C extp o

  (** Program *)

  | red_prog_intro : forall S C0 str pis o,
      (* TODO: initialize the execution context with binding instantiation *)
      red_prog S (execution_ctx_initial str) (prog_1 resvalue_empty els) o ->
      red_prog S C0 (prog_intro str els) o

  (** No more source elements *)

  | red_prog_1_nil : forall S C rv,
      red_prog S C (prog_1 rv nil) (out_ter S rv)

  (** Source element : statement (recall [abort_intercepted_prog]) *)

  | red_prog_1_cons_stat : forall S C t rv els o1 o,
      red_stat S C t o1 ->
      red_prog S C (prog_2 rv o1 els) o ->
      red_prog S C (prog_1 rv ((element_stat t)::els)) o

  | red_prog_2 : forall S0 S C R rv els o,
      res_type R <> restype_throw ->
      red_prog S C (prog_3 (out_ter S (res_overwrite_value_if_empty rv R)) els) o ->
      red_prog S0 C (prog_2 rv (out_ter S R) els) o

  | red_prog_3 : forall S0 S C rv els o,
      red_prog S C (prog_1 rv els) o ->
      red_prog S0 C (prog_3 (out_ter S rv) els) o

  (** Source element : function declaration *)

  | red_prog_1_cons_funcdecl : forall S C rv name args bd els o,
      red_prog S C (prog_1 rv els) o ->
      red_prog S C (prog_1 rv ((element_func_decl name args bd)::els)) o


(**************************************************************)
(** ** Reduction rules for statements (13) *)

with red_stat : state -> execution_ctx -> ext_stat -> out -> Prop :=

  (** Abort rule for statements *)

  | red_stat_abort : forall S C extt o,
      out_of_ext_stat text = Some o ->
      abort o ->
      ~ abort_intercepted_stat extt ->
      red_stat S C extt o

  (** Block statement (recall [abort_intercepted_stat]) *)

  | red_stat_block : forall S C ts o,
      red_stat S C (stat_block_1 res_empty ts) o ->
      red_stat S C (stat_block ts) o

  | red_stat_block_1_nil : forall S C rv,
      red_stat S C (stat_block_1 rv nil) (out_ter S rv)

  | red_stat_block_1_cons : forall S C rv t ts o1 o,
      red_stat S C t o1 ->
      red_stat S C (stat_block_2 rv o1 ts) o ->
      red_stat S C (stat_block_1 rv (t::ts)) o

  | red_stat_block_2 : forall S0 S C ts R rv o,
      res_type R <> restype_throw ->
      red_stat S C (stat_block_3 (out_ter S (res_overwrite_value_if_empty rv R)) ts) o ->
      red_stat S0 C (stat_block_2 rv (out_ter S R) ts) o

  | red_stat_block_3 : forall S0 S C ts rv o,
      red_stat S C (stat_block_1 rv ts) o ->
      red_stat S0 C (stat_block_3 (out_ter S rv) ts) o

  (** Variable declaration *)

  | red_stat_var_decl_nil : forall S C, 
      red_stat S C (stat_var_decl nil) (out_ter S res_empty)

  | red_stat_var_decl_cons : forall S C o o1 d ds, 
      red_stat S C (stat_var_decl_item d) o1 ->
      red_stat S C (stat_var_decl_1 o1 ds) o ->
      red_stat S C (stat_var_decl (d::ds)) o

  | red_stat_var_decl_1 : forall S S0 C ds o rv, 
      red_stat S C (stat_var_decl ds) o ->
      red_stat S0 C (stat_var_decl_1 (out_ter S rv) ds) o

  | red_stat_var_decl_item_none : forall S C x, 
      red_stat S C (stat_var_decl_item (x,None)) (out_ter S x)

  | red_stat_var_decl_item_some : forall S C x e o o1, 
      red_expr S C (spec_identifier_resolution C x) o1 ->
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
  
  | red_stat_var_decl_item_3 : forall S S0 C x r rv, 
      red_stat S0 C (stat_var_decl_item_3 x (out_ter S rv)) (out_ter S x)

  (** Expression *)

  | red_stat_expr : forall S C e o,
      red_expr S C (spec_expr_get_value e) o ->
      red_stat S C (stat_expr e) o

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

  (** Do-while statement (recall [abort_intercepted_stat]) *)

  | red_stat_do_while : forall S C labs t1 e2 o,
      red_stat S C (stat_do_while_1 labs t1 e2 resvalue_empty) o ->
      red_stat S C (stat_do_while labs t1 e2) o

  | red_stat_do_while_1 : forall S C labs t1 e2 rv o1 o,
      red_stat S C t1 o1 ->
      red_stat S C (stat_do_while_2 labs t1 e2 rv o1) o ->
      red_stat S C (stat_do_while_1 labs t1 e2 rv) o

  | red_stat_do_while_2_true : forall S0 S C labs t1 e2 rv_old rv o1 o,
      rv = (If res_value R = resvalue_empty then rv_old else res_value R) ->
      red_stat S C (stat_do_while_3 labs t1 e2 rv R) o ->
      red_stat S0 C (stat_do_while_2 labs t1 e2 rv_old (out_ter S R)) o 

  | red_stat_do_while_3_break : forall S0 S C labs t1 e2 rv R,
      res_type R = restype_break ->
      res_label_in R labs ->
      red_stat S C (stat_do_while_3 labs t1 e2 rv R) (out_ter S rv)

  | red_stat_do_while_3_not_break : forall S0 S C labs t1 e2 rv R o,
      ~ (res_type R = restype_break /\ res_label_in R labs) ->
      red_stat S C (stat_do_while_4 labs t1 e2 rv) o ->      
      red_stat S C (stat_do_while_3 labs t1 e2 rv R) o

  | red_stat_do_while_4 : forall S0 S C labs t1 e2 rv R o,
      red_stat S C (spec_expr_get_value_conv_stat e2 spec_to_boolean (stat_do_while_5 labs t1 e2 rv)) o ->
      red_stat S C (stat_do_while_4 labs t1 e2 rv) o

  | red_stat_do_while_5_false : forall S C labs t1 e2 rv,
      red_stat S C (stat_do_while_5 labs t1 e2 rv false)) (out_ter S rv)

  | red_stat_do_while_5_true : forall S C labs t1 e2 rv o,
      red_stat S C (stat_do_while_1 labs t1 e2 rv) o ->
      red_stat S C (stat_do_while_5 labs t1 e2 rv true)) o

  (** While statement (recall [abort_intercepted_stat]) *)

  | red_stat_while : forall S C labs e1 t2 o,
      red_stat S C (stat_while_1 labs e1 t2 resvalue_empty) o ->
      red_stat S C (stat_while labs e1 t2) o

  | red_stat_while_1 : forall S C labs e1 t2 rv o,
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_boolean (stat_while_2 labs e1 t2 rv)) o ->
      red_stat S C (stat_while_1 labs e1 t2 rv) o

  | red_stat_while_2_false : forall S C labs e1 t2 rv,
      red_stat S C (stat_while_2 labs e1 t2 rv false)) (out_ter S rv)

  | red_stat_while_2_true : forall S C labs e1 t2 rv o1 o,
      red_stat S C t2 o1 ->
      red_stat S C (stat_while_3 labs e1 t2 rv o1) o ->
      red_stat S C (stat_while_2 labs e1 t2 rv true)) o

  | red_stat_while_3_true : forall S0 S C labs e1 t2 rv_old rv o1 o,
      rv = (If res_value R = resvalue_empty then rv_old else res_value R) ->
      red_stat S C (stat_while_4 labs e1 t2 rv R) o ->
      red_stat S0 C (stat_while_3 labs e1 t2 rv_old (out_ter S R)) o 

  | red_stat_while_4_break : forall S0 S C labs e1 t2 rv R,
      res_type R = restype_break ->
      res_label_in R labs ->
      red_stat S C (stat_while_4 labs e1 t2 rv R) (out_ter S rv)

  | red_stat_while_4_not_break : forall S0 S C labs e1 t2 rv R o,
      ~ (res_type R = restype_break /\ res_label_in R labs) ->
      red_stat S C (stat_while_1 labs e1 t2 rv) o ->      
      red_stat S C (stat_while_4 labs e1 t2 rv R) o

  (** For statement: LATER *)

  (** For-in statement: LATER *)

  (** Continue statement *)

  | red_stat_continue : forall S C labo,
      red_stat S C (stat_continue labo) (out_ter S (res_continue labo))

  (** Break statement *)

  | red_stat_break : forall S C labo,
      red_stat S C (stat_break labo) (out_ter S (res_break labo))

  (** Return statement *)
  
  | red_stat_return_none : forall S C,
      red_stat S C (stat_return None) (out_ter S (res_return undef))

  | red_stat_return_some : forall S C e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_return_1 o1) o ->
      red_stat S C (stat_return (Some e)) o

  | red_stat_return_some_1 : forall S0 S C v,
      red_stat S0 C (stat_return_1 (out_ter S v)) (out_ter S (res_return v))

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
      (* TODO: i'm not sure how to interpret step 7 of 12.10 *)

  (** Switch statement : LATER *)

  (** Labelled statement (recall [abort_intercepted_stat]) *)

  | red_stat_label : forall S C lab t o1 o,
      red_stat S C t o1 ->
      red_stat S C (stat_label_1 lab o1) o ->
      red_stat S C (stat_label lab t) o

  | red_stat_label_1_normal : forall S0 S lab C rv,
      red_stat S0 C (stat_label_1 lab (out_ter S rv)) (out_ter S rv)

  | red_stat_label_1_break_eq : forall S0 S C R rv lab,
      R = res_intro restype_break rv (Some lab) ->
      red_stat S0 C (stat_label_1 lab (out_ter S R)) (out_ter S (res_normal rv))

 (** Throw statement *)

  | red_stat_throw : forall S C e o o1,
      red_expr S C (spec_expr_get_value e) o1 ->
      red_stat S C (stat_throw_1 o1) o ->
      red_stat S C (stat_throw e) o

  | red_stat_throw_1 : forall S0 S C v,
      red_stat S0 C (stat_throw_1 (out_ter S v)) (out_ter S (res_throw v))

  (** Try statement (recall [abort_intercepted_stat]) *)

  | red_stat_try : forall S C t co fo o o1,
      red_stat S C t o1 ->
      red_stat S C (stat_try_1 o1 co fo) o ->
      red_stat S C (stat_try t co fo) o

  | red_stat_try_1_no_throw : forall S0 S C R co fo o,
      res_type R <> restype_throw ->
      red_stat S0 C (stat_try_4 R fo) o ->
      red_stat S0 C (stat_try_1 (out_ter S R) co fo) o

  | red_stat_try_1_throw_no_catch : forall S0 S C R co fo o,
      res_type R = restype_throw ->
      red_stat S0 C (stat_try_4 R fo) o ->
      red_stat S0 C (stat_try_1 (out_ter S R) None fo) o

  | red_stat_try_1_throw_catch : forall S0 S S' C lex lex' oldlex L x R t1 fo o1 o,
      res_type R = restype_throw ->
      lex = execution_ctx_lexical_env C ->
      (lex',S') = lexical_env_alloc_decl S lex ->
      lex' = L::oldlex -> (* Note: oldlex is in fact equal to lex *)
      red_expr S' C (spec_env_record_create_set_mutable_binding L x None (res_value R) throw_irrelevant) o1 ->
      red_stat S' C (stat_try_2 o1 lex' t1 fo) o ->
      red_stat S0 C (stat_try_1 (out_ter S R) (Some (x,t1)) fo) o

  | red_stat_try_2_catch : forall C S0 S lex' t1 fo o o1,
      red_stat S (execution_ctx_with_lex C lex') t1 o1 ->
      red_stat S C (stat_try_3 o1 fo) o ->
      red_stat S0 C (stat_try_2 (out_ter_void S) lex' t1 fo) o

  | red_stat_try_3_catch_result : forall S C R fo o,
      red_stat S C (stat_try_4 R fo) o ->
      red_stat S0 C (stat_try_3 (out_ter S R) fo) o

  | red_stat_try_4_no_finally : forall S C R,
      red_stat S C (stat_try_4 R None) (out_ter S R)

  | red_stat_try_4_finally : forall S C R t1 o o1,
      red_stat S C t1 o1 ->
      red_stat S C (stat_try_5 R o1) o ->
      red_stat S C (stat_try_4 R (Some t1)) o

  | red_stat_try_5_finally_result : forall S0 S C R rv,
      red_stat S0 C (stat_try_5 R (out_ter S rv)) (out_ter S R) 

  (** Debugger statement *)
  
  | res_stat_debugger : forall S C,
      red_stat S C stat_debugger (out_ter S res_empty)

  (* Auxiliary forms : [spec_expr_get_value] plus a type conversion 
     for statements *)

  | red_spec_expr_get_value_conv_stat : forall S C e sc K o o1, (* TODO: rename sc *)
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
(** ** Reduction rules for expressions (11) *)

with red_expr : state -> execution_ctx -> ext_expr -> out -> Prop :=

  (** Abort rule for expressions *)

  | red_expr_abort : forall S C exte o,
      out_of_ext_expr exte = Some o ->
      abort o ->
      red_expr S C exte o

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

  | red_expr_identifier : forall S C x o,
      red_expr S C (spec_identifier_resolution C x) o ->
      red_expr S C (expr_identifier x) o

  (** Literal *)

  | red_expr_literal : forall S C s i v,
      v = convert_literal_to_prim i ->
      red_expr S C (expr_literal i) (out_ter S v)

  (** Array initializer : LATER *)

  (** Object initializer *)
  
  | red_expr_object : forall S C pds o1 o, 
      red_expr S C (spec_constructor_builtin builtin_object_new nil) o1 ->
      red_expr S C (expr_object_1 o1 pds) o ->
      red_expr S C (expr_object pds) o
 
  | red_expr_object_0 : forall S0 S C l pds o, 
      red_expr S C (expr_object_1 l pds) o ->
      red_expr S0 C (expr_object_0 (out_ter S l) pds) o ->
          
  | red_expr_object_1_nil : forall S S C l, 
      red_expr S C (expr_object_1 l nil) (out_ter S l)
  
  | red_expr_object_1_cons : forall S0 S C x l pn pb pds o, 
      x = string_of_propname pn ->
      red_expr S C (expr_object_2 l x pb pds) o ->
      red_expr S C (expr_object_1 l ((pn,pb)::pds)) o

  | red_expr_object_2_val : forall S C e o o1 l x pds, 
      red_expr S C (spec_expr_get_value e) o1 ->
      red_expr S C (expr_object_3_val l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_val e) pds) o

  | red_expr_object_3_val : forall S S0 C l x A v o pds,
      A = prop_attributes_create_data v true true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_val l x (out_ter S v) pds) o
  
  | red_expr_object_2_get : forall S C bd l x o o1 pds,
      red_expr S C (spec_create_new_function_in C nil bd) o1 ->
      red_expr S C (expr_object_3_get l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_get bd) pds) o
  
  | red_expr_object_3_get : forall S S0 C A l x v pds o,  
      A = prop_attributes_create_accessor_opt None (Some v) true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_get l x (out_ter S v) pds) o

  | red_expr_object_2_set : forall S S0 C A l x v pds o o1 bd args,
      red_expr S C (spec_create_new_function_in C args bd) o1 ->
      red_expr S C (expr_object_3_set l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_set args bd) pds) o

  | red_expr_object_3_set : forall S S0 C A l x v pds o,
      A = prop_attributes_create_accessor_opt (Some v) None true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_set l x (out_ter S v) pds) o
  
  | red_expr_object_4_define_own_prop : forall S S0 C A l x v pds o o1,
      red_expr S C (spec_object_define_own_prop l x A false) o1 ->
      red_expr S C (expr_object_5 l pds o1) o ->
      red_expr S C (expr_object_4 l x A pds) o

  | red_expr_object_5_next_property : forall S S0 rv C A l x v pds o,
      red_expr S C (expr_object_1 l pds) o ->
      red_expr S0 C (expr_object_5 l pds (out_ter S rv)) o   

  (** Member *)

  | red_expr_member : forall x S0 C e1 o,
      red_expr S0 C (expr_access e1 (expr_literal (literal_string x))) o ->
      red_expr S0 C (expr_member e1 x) o

  (** Access *)

  | red_expr_access : forall S C e1 e2 o o1,
      red_expr S C (spec_expr_get_value e1) o1 ->
      red_expr S C (expr_access_1 o1 e2) o ->
      red_expr S C (expr_access e1 e2) o
      
  | red_expr_access_1 : forall S0 S C v1 o o1 e2,
      red_expr S C (spec_expr_get_value e2) o1 ->
      red_expr S C (expr_access_2 v1 o1) o ->
      red_expr S0 C (expr_access_1 (out_ter S v1) e2) o
      
  | red_expr_access_2 : forall S0 S C v1 v2 o1 o,
      red_expr S C (spec_check_object_coercible v1) o1 ->
      red_expr S C (expr_access_3 v1 o1 v2) o ->
      red_expr S0 C (expr_access_2 v1 (out_ter S v2)) o

  | red_expr_ext_expr_access_3 : forall S0 S C v1 v2 o1 o,
      red_expr S C (spec_to_string v2) o1 ->
      red_expr S C (expr_access_4 v1 o1) o ->
      red_expr S0 C (expr_access_3 v1 (out_ter_void S) v2) o

  | red_expr_ext_expr_access_4 : forall S0 S C v1 x r,
     r = ref_create_value v1 x (execution_ctx_strict C) ->
     red_expr S0 C (expr_access_4 v1 (out_ter S x)) (out_ter S r)


(*---start todo---*)

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

  | red_expr_call_1 : forall o1 S0 S C o rv e2s,
      red_expr S C (spec_get_value rv) o1 ->
      red_expr S C (expr_call_2 rv e2s o1) o ->
      red_expr S0 C (expr_call_1 (out_ter S rv) e2s) o
      
  | red_expr_call_2 : forall S0 S C o rv v e2s,
      red_expr S C (expr_list_then (expr_call_3 rv v) e2s) o ->
      red_expr S0 C (expr_call_2 rv e2s (out_ter S v)) o
      
  | red_expr_call_3_not_object : forall S C o rv v vs,
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_call_3 rv v vs) o
      
  | red_expr_call_3_not_callable : forall S C o rv l vs,
      ~ (is_callable S l) ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (expr_call_3 rv (value_object l) vs) o
      
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

  (** Function expression *)

  | red_expr_function_unnamed : forall S C args bd o,
      red_expr S C (spec_creating_function_object args bd (execution_ctx_lexical_env C) (funcbody_is_strict bd)) o ->
      red_expr S C (expr_function None args bd) o 

  | red_expr_function_named : forall lex' S' L lextail E o1 S C s args bd o,
      (lex', S') = lexical_env_alloc_decl S (execution_ctx_lexical_env C) ->
      lex' = L :: lextail ->
      env_record_binds S' L E ->
      red_expr S' C (spec_env_record_create_immutable_binding L s) o1 ->
      red_expr S' C (expr_function_1 s args bd L lex' o1) o -> 
      red_expr S C (expr_function (Some s) args bd) o 
      
  | red_expr_function_named_1 : forall o1 S0 S C s args bd L scope o,
      red_expr S C (spec_creating_function_object args bd scope (funcbody_is_strict bd)) o1 ->
      red_expr S C (expr_function_2 s L o1) o ->
      red_expr S0 C (expr_function_1 s args bd L scope (out_ter_void S)) o
      
  | red_expr_function_named_2 : forall o1 S0 S C s L l o,
      red_expr S C (spec_env_record_initialize_immutable_binding L s l) o1 ->
      red_expr S C (expr_function_3 l o1) o ->
      red_expr S0 C (expr_function_2 s L (out_ter S l)) o  
      
  | red_expr_function_named_3 : forall S0 S C l,
      red_expr S0 C (expr_function_3 l (out_ter_void S)) (out_ter S l) 

(*---end todo---*)

  (** Unary op : pre/post incr/decr *)

  | red_expr_prepost : forall S C op e o1 o,
      prepost_unary_op op ->
      red_expr S C e o1 ->
      red_expr S C (expr_prepost_1 op o1) o ->
      red_expr S C (expr_unary_op op e) o

  | red_expr_prepost_1_valid : forall S0 S C rv op o1 o,
      red_expr S C (spec_get_value rv) o1 ->
      red_expr S C (expr_prepost_2 op rv o1) o ->
      red_expr S0 C (expr_prepost_1 op (out_ter S rv)) o
 
  | red_expr_prepost_2 : forall S0 S C rv op v o1 o,    
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (expr_prepost_3 op rv o1) o ->
      red_expr S0 C (expr_prepost_2 op rv (out_ter S v)) o
 
  | red_expr_prepost_3 : forall S0 S C rv op number_op is_pre v n1 n2 o1 o,  
      prepost_op op number_op is_pre ->
      n2 = number_op n1 ->
      v = prim_number (if is_pre then n2 else n1) ->
      red_expr S C (spec_put_value rv n2) o1 ->
      red_expr S C (expr_prepost_4 v o1) o ->
      red_expr S0 C (expr_prepost_3 op rv (out_ter S n1)) o
 
  | red_expr_prepost_4 : forall S0 S C v,  
      red_expr S0 C (expr_prepost_4 v (out_ter_void S)) (out_ter S v)

  (** Unary op -- common rules for regular operators *)

  | red_expr_unary_op : forall S C op e o1 o,
      regular_unary_op op ->
      red_expr S C (spec_expr_get_value e) o1 ->
      red_expr S C (expr_unary_op_1 op o1) o ->
      red_expr S C (expr_unary_op op e) o

  | red_expr_unary_op_1 : forall S0 S C op v o,
      red_expr S C (expr_unary_op_2 op v) o ->
      red_expr S0 C (expr_unary_op_1 op (out_ter S v)) o

  (** Unary op : delete (not a regular op) *)

  | red_expr_delete : forall S C e o1 o,
      red_expr S C e o1 ->
      red_expr S C (expr_delete_1 o1) o ->
      red_expr S C (expr_unary_op unary_op_delete e) o

  | red_expr_delete_1_not_ref : forall S0 S C rv,
      ~ (resvalue_is_ref rv) ->
      red_expr S0 C (expr_delete_1 (out_ter S rv)) (out_ter S true)

  | red_expr_delete_1_ref_unresolvable : forall S0 S C rv,
      ref_is_unresolvable r ->
      red_expr S0 C (expr_delete_1 (out_ter S r)) (out_ter S true)

  | red_expr_delete_1_ref_property : forall S0 S C r v o1 o,
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (expr_delete_2 r o1) o ->
      red_expr S0 C (expr_delete_1 (out_ter S r)) o

  | red_expr_delete_2 : forall S0 S C x l str o,
      red_expr S C (spec_object_delete l (ref_name r) (ref_strict r)) o ->
      red_expr S0 C (expr_delete_2 r (out_ter S l)) o

  | red_expr_delete_1_ref_env_record : forall S0 S C r L o,
      ref_is_env_record r L ->
      red_expr S C (spec_env_record_delete_binding L (ref_name r)) o ->
      red_expr S0 C (expr_delete_1 (out_ter S r)) o
    
  (** Unary op : void *)

  | red_expr_unary_op_void : forall S C v,
      red_expr S C (expr_unary_op_2 unary_op_void v) (out_ter S undef)

  (** Unary op : typeof (not a regular op) *)

  | red_expr_typeof : forall S C e o1 o,
      red_expr S C e o1 ->
      red_expr S C (expr_typeof_1 o1) o ->
      red_expr S C (expr_unary_op unary_op_typeof e) o

  | red_expr_typeof_1_value : forall S0 S C v o,
      red_expr S C (expr_typeof_2 (out_ter S v)) o ->
      red_expr S0 C (expr_typeof_1 (out_ter S v)) o

  | red_expr_typeof_1_ref_unresolvable : forall S0 S r C,
      ref_is_unresolvable r ->
      red_expr S0 C (expr_typeof_1 (out_ter S r)) (out_ter S "undefined")

  | red_expr_typeof_1_ref_resolvable : forall S0 S C rv o1 o,
      ~ (ref_is_unresolvable r) ->
      red_expr S C (spec_get_value r) o1 ->
      red_expr S C (expr_typeof_2 o1) o ->
      red_expr S0 C (expr_typeof_1 (out_ter S r)) o

  | red_expr_typeof_2 : forall S0 S s C v o,
      s = typeof_value S v ->
      red_expr S0 C (expr_typeof_2 (out_ter S v)) (out_ter S s)

  (** Unary op : add *)

  | red_expr_unary_op_add : forall S C v o,
      red_expr S C (spec_to_number v) o ->
      red_expr S C (expr_unary_op_2 unary_op_add v) o

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

  (** Binary op -- common rules for regular operators *)

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
      red_expr S C (spec_convert_twice (spec_to_primitive_auto v1) (spec_to_primitive_auto v2) expr_binary_op_add_1) o ->
      red_expr S C (expr_binary_op_3 binary_op_add v1 v2) o

  | red_expr_binary_op_add_1_string : forall S C v1 v2 o,
      (type_of v1 = type_string \/ type_of v2 = type_string) ->
      red_expr S C (spec_convert_twice (spec_to_string v1) (spec_to_string v2) expr_binary_op_add_string_1) o ->
      red_expr S C (expr_binary_op_add_1 v1 v2) o

  | red_expr_binary_op_add_string_1 : forall S C s1 s2 s o,
      s = string_concat s1 s2 ->
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
      red_expr S C (spec_convert_twice (spec_to_primitive_auto v1) (spec_to_primitive_auto v2) (expr_inequality_op_2 b_swap b_neg)) o ->
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

  | red_expr_binary_op_instanceof_normal : forall B S C v1 l o,
      object_has_instance S l (Some B) ->
      red_expr S C (spec_object_has_instance B l v1) o ->
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
        else If (T1 = type_string \/ T1 = type_number) /\ T2 = type_object then (spec_equal_3 v1 spec_to_primitive_auto v2)
        else If T1 = type_object /\ (T2 = type_string \/ T2 = type_number) then (spec_equal_3 v2 spec_to_primitive_auto v1)
        else (spec_equal_2 false)) ->
      red_expr S C ext o ->
      red_expr S C (spec_equal_1 T1 T2 v1 v2) o

  | red_spec_equal_2_return : forall S C b,
      red_expr S C (spec_equal_2 b) (out_ter S b)

  | red_spec_equal_3_convert_and_recurse : forall S C v1 v2 K o2 o,
      red_expr S C (K v2) o2 ->
      red_expr S C (spec_equal_4 v1 o2) o ->
      red_expr S C (spec_equal_3 v1 K v2) o

  | red_spec_equal_4_recurse : forall S0 S C v1 v2 o,
      red_expr S C (spec_equal v1 v2) o ->    
      red_expr S0 C (spec_equal_4 v1 (out_ter S v2)) o

  (** Binary op : str equality/disequality *)

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

  (** Binary op : lazy ops [and] and [or] (not regular ops) *)

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

  (** Assignment *)
  
  | red_expr_assign : forall S C opo e1 e2 o o1,
      red_expr S C e1 o1 ->
      red_expr S C (expr_assign_1 o1 opo e2) o ->
      red_expr S C (expr_assign e1 opo e2) o
 
  | red_expr_assign_1_simple : forall S0 S C rv e2 o o1,
      red_expr S C (spec_expr_get_value e2) o1 ->
      red_expr S C (expr_assign_4 rv o1) o ->
      red_expr S0 C (expr_assign_1 (out_ter S rv) None e2) o

  | red_expr_assign_1_compound : forall S0 S C rv op e2 o o1,
      red_expr S C (spec_get_value rv) o1 ->
      red_expr S C (expr_assign_2 rv o1 op e2) o ->
      red_expr S0 C (expr_assign_1 (out_ter S rv) (Some op) e2) o

  | red_expr_assign_2_compound_get_value : forall S0 S C rv op v1 o2 e2 o,
      red_expr S C (spec_expr_get_value e2) o2 ->
      red_expr S C (expr_assign_3 rv v1 op o2) o ->
      red_expr S0 C (expr_assign_2 rv (out_ter S v1) op e2) o

  | red_expr_assign_3_compound_op : forall S0 S C rv op v1 v2 o1 o,
      red_expr S C (expr_binary_op_3 op v1 v2) o1 ->
      red_expr S C (expr_assign_4 rv o1) o ->
      red_expr S0 C (expr_assign_3 rv v1 op (out_ter S v2)) o

  | red_expr_assign_4_put_value : forall S0 S C rv v o1 o,
      red_expr S C (spec_put_value rv v) o1 ->
      red_expr S C (expr_assign_5 v o1) o ->
      red_expr S0 C (expr_assign_4 rv (out_ter S v)) o

  | red_expr_assign_5_return : forall S0 S C rv' v,
      red_expr S0 C (expr_assign_5 v (out_ter S rv')) (out_ter S v)

  (** Conditional operator *)

  | red_expr_conditional : forall S C e1 e2 e3 o o1,
      red_expr S C (spec_expr_get_value_conv spec_to_boolean e1) o1 ->
      red_expr S C (expr_conditional_1 o1 e2 e3) o ->
      red_expr S C (expr_conditional e1 e2 e3) o

  | red_expr_conditional_1 : forall S0 S C e b e2 e3 o,
      e = (If b = true then e2 else e3) ->
      red_expr S C (spec_expr_get_value e) o ->
      red_expr S0 C (expr_conditional_1 (out_ter S b) e2 e3) o

  (** Coma (represented as a binary operator) *)

  | red_expr_binary_op_coma : forall S C v1 v2,
      red_expr S C (expr_binary_op_3 binary_op_coma v1 v2) (out_ter S v2)


(**************************************************************)
(** ** Reduction rules for specification functions *)

  (** Special function *)

  | red_spec_returns : forall S C o,
      red_expr S C (spec_returns o) o


  (*------------------------------------------------------------*)
  (** ** Conversions (9) *)

  (** Conversion to primitive (returns prim) *)

  | red_spec_to_primitive_pref_prim : forall S C w prefo,
      red_expr S C (spec_to_primitive (value_prim w) prefo) (out_ter S w)

  | red_spec_to_primitive_pref_object : forall S C l prefo o,
      red_expr S C (spec_to_default l prefo) o ->
      red_expr S C (spec_to_primitive (value_object l) prefo) o

  (** Conversion to bool (returns bool) *)

  | red_spec_to_boolean : forall S C v b,
      b = convert_value_to_boolean v ->
      red_expr S C (spec_to_boolean v) (out_ter S b)

  (** Conversion to number (returns number) *)

  | red_spec_to_number_prim : forall S C w n,
      n = convert_prim_to_number w ->
      red_expr S C (spec_to_number (value_prim w)) (out_ter S n)

  | red_spec_to_number_object : forall S C l o1 o,
      red_expr S C (spec_to_primitive (value_object l) (Some preftype_number)) o1 ->
      red_expr S C (spec_to_number_1 o1) o ->
      red_expr S C (spec_to_number (value_object l)) o

  | red_spec_to_number_1 : forall S0 S C w n,
      n = convert_prim_to_number w ->
      red_expr S0 C (spec_to_number_1 (out_ter S w)) (out_ter S n)

  (** Conversion to integer (returns number) *)

  | red_spec_to_integer : forall S C v o1 o,
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_to_integer_1 o1) o ->
      red_expr S C (spec_to_integer v) o

  | red_spec_to_integer_1 : forall S0 S C n n',
      n' = convert_number_to_integer n ->
      red_expr S0 C (spec_to_integer_1 (out_ter S n)) (out_ter S n')

  (** Conversion to 32-bit integer (passes an int to the continuation) *)

  | red_spec_to_int32 : forall S C v  K o1 o,
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_to_int32_1 o1 K) o ->
      red_expr S C (spec_to_int32 v K) o

  | red_spec_to_int32_1 : forall S0 S C n K o,
      red_expr S C (K (JsNumber.to_int32 n)) o ->
      red_expr S0 C (spec_to_int32_1 (out_ter S n) K) o

   (** Conversion to unsigned 32-bit integer (passes an int to the continuation) *)

  | red_spec_to_uint32 : forall S C v  K o1 o,
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_to_uint32_1 o1 K) o ->
      red_expr S C (spec_to_uint32 v K) o

  | red_spec_to_int32_1 : forall S0 S C n K o,
      red_expr S C (K (JsNumber.to_uint32 n)) o ->
      red_expr S0 C (spec_to_uint32_1 (out_ter S n) K) o
  
  (** Conversion to unsigned 16-bit integer (passes an int to the continuation) : LATER *)

  (** Conversion to string (returns string) *)

  | red_spec_to_string_prim : forall S C w s,
      s = convert_prim_to_string w ->
      red_expr S C (spec_to_string (value_prim w)) (out_ter S s)

  | red_spec_to_string_object : forall S C l o1 o,
      red_expr S C (spec_to_primitive (value_object l) (Some preftype_string)) o1 ->
      red_expr S C (spec_to_string_1 o1) o ->
      red_expr S C (spec_to_string (value_object l)) o

  | red_spec_to_string_1 : forall S0 S C w s,
      s = convert_prim_to_string w ->
      red_expr S0 C (spec_to_string_1 (out_ter S w)) (out_ter S s)

  (** Conversion to object (returns object_loc) *)

  | red_spec_to_object_undef_or_null : forall S C v o,
      v = prim_undef \/ v = prim_null ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_to_object v) o

  | red_spec_to_object_prim : forall S C o,
      prim_convertible_to_object w ->
      red_expr S C (spec_prim_new_object w) o ->
      red_expr S C (spec_to_object (value_prim w)) o

  | red_spec_to_object_object : forall S C l,
      red_expr S C (spec_to_object (value_object l)) (out_ter S l)

  (** Check object coercible (returns void) *)

  | red_spec_check_object_coercible_undef_or_null : forall S C v o,
      v = prim_undef \/ v = prim_null ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_to_object v) o

  | red_spec_check_object_coercible_return : forall S C v,
      ~ (v = prim_undef \/ v = prim_null) ->
      red_expr S C (spec_check_object_coercible v) (out_ter_void S)

  (** Auxiliary: conversion of two values at once (passes two values to the continuation) *)

  | red_spec_convert_twice : forall S C ex1 ex2 o1 K o,
      red_expr S C ex1 o1 ->
      red_expr S C (spec_convert_twice_1 o1 ex2 K) o ->
      red_expr S C (spec_convert_twice ex1 ex2 K) o

  | red_spec_convert_twice_1 : forall S0 S C v1 ex2 o2 K o,
      red_expr S C ex2 o2 ->
      red_expr S C (spec_convert_twice_2 o2 (K v1)) o ->
      red_expr S0 C (spec_convert_twice_1 (out_ter S v1) ex2 K) o

  | red_spec_convert_twice_2 : forall S0 S C v2 K o,
      red_expr S C (K v2) o ->
      red_expr S0 C (spec_convert_twice_2 (out_ter S v2) K) o


  (*------------------------------------------------------------*)
  (** ** Operations on objects (8.12, but also elsewhere) *)

  (** GetOwnProperty (passes a property descriptor to the continuation) *)

  | red_spec_object_get_own_property : forall S C l x K o,
      object_method object_get_own_property_ S l B ->
      red_expr S C (spec_object_get_own_property_1 B l x K) o ->
      red_expr S C (spec_object_get_own_property l x K) o  

  (** GetOwnProperty, default  (8.12.1) *)

  | red_spec_object_get_own_property_1_default : forall S C l x K An o,
      (* TODO: change def used on next list into reductions *)
      object_get_own_property S l x An ->
      red_expr S C (K An) o ->  
      red_expr S C (spec_object_get_own_property builtin_default_get_own_property l x K) o  

  (* TODO: define here [get_own_property] for function arguments, arrays and strings *)

  (** GetProperty (passes a property descriptor to the continuation)  *)

  | red_spec_object_get_property : forall S C l x K o,
      object_method object_get_property_ S l B ->
      red_expr S C (spec_object_get_property_1 B l x K) o ->
      red_expr S C (spec_object_get_property l x K) o  

  (** GetProperty, default  (8.12.2) *)

  | red_spec_object_get_property_1_default : forall S C l x An o,
      (* TODO: change def used on next list into reductions *)
      object_get_property S (value_object l) x An ->
      red_expr S C (K An) o ->  
      red_expr S C (spec_object_get_property builtin_default_get_property l x K) o  
  
  (** Get (returns value) *)

  | red_spec_object_get : forall S C l x o,
      object_method object_get_ S l B ->
      red_expr S C (spec_object_get_1 B l x) o ->
      red_expr S C (spec_object_get l x) o  

  (** Get, default  (8.12.3) *)

  | red_spec_object_get_1_default : forall S C l x An o,
      red_expr S C (spec_object_get_property l x (spec_object_get_default_1 l)) o ->      
      red_expr S C (spec_object_get builtin_default_get l x) o  

  | red_spec_object_get_default_1_undef : forall S C l,
      red_expr S C (spec_object_get_default_1 l prop_descriptor_undef) (out_ter S undef)

  | red_spec_object_get_default_1_some_data : forall S C l A v,
      prop_attributes_is_data A ->
      prop_attributes_value A = Some v ->
      red_expr S C (spec_object_get_default_1 l (prop_descriptor_some A)) (out_ter S v)

  | red_spec_object_get_default_1_some_accessor : forall S C l A o,
      prop_attributes_is_accessor A ->
      red_expr S C (spec_object_get_default_2 l (prop_attributes_get A)) o ->
      red_expr S C (spec_object_get_default_1 l (prop_descriptor_some A)) o

  | red_spec_object_get_default_2_no_getter : forall S C l,
      red_expr S C (spec_object_get_default_2 l None) (out_ter S undef) 

  | red_spec_object_get_default_2_getter : forall builtinid S C l lf o,
      object_call S lf (Some builtinid) ->
      red_expr S C (spec_call builtinid (Some lf) (Some (value_object l)) nil) o ->
      red_expr S C (spec_object_get_default_2 l (Some (value_object lf))) o
      
(*---start todo---*)
  (** Get, functions  (8.12.3) *)

(* handle get for functions 
   red_expr S C (spec_object_get builtin_functon_get l x K) o  

  | red_spec_object_function_get : forall o1 S C l x o,
      red_expr S C (spec_object_object_get l x) o1 ->
      red_expr S C (spec_object_function_get_1 l x o1) o ->
      red_expr S C (spec_object_function_get l x) o
      
  | red_spec_object_function_get_1_error : forall bd S0 S C l v o,
      object_code S l (Some bd) ->
      funcbody_is_strict bd = true ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S0 C (spec_object_function_get_1 l "caller" (out_ter S v)) o
   
  | red_spec_object_function_get_1 : forall bd S0 S C l x v o,
      (object_code S l (Some bd) /\ funcbody_is_strict bd = false) \/ (x <> "caller") \/ (object_code S l None) ->
      red_expr S0 C (spec_object_function_get_1 l x (out_ter S v)) (out_ter S v)

     (* TODO: see 15.3.5.4 for a special get method for functions;
         also arrays & string have special stuff *)
*)

  (* TODO: get for arrays and strings *)
(*---end todo---*)

  (** Special get method for primitive values (returns value)  (TODO: section ??) *)

  | red_spec_object_get_special : forall o1 S C v x o,
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (spec_object_get_special_1 v x o1) o ->
      red_expr S C (spec_object_get_special v x) o

  | red_spec_object_get_special_1 : forall S0 C v x S l o,
      red_expr S C (spec_object_get_using v l x) o ->
      (* TODO: spec_object_get_using is like spec_object_get except that the this value is different *)
      red_expr S0 C (spec_object_get_special_1 v x (out_ter S l)) o

  (** CanPut (returns bool) *)

  | red_spec_object_can_put : forall S C l x o,
      object_method object_can_put_ S l B ->
      red_expr S C (spec_object_can_put_1 B l x) o ->
      red_expr S C (spec_object_can_put l x) o  

  (** CanPut, default  (8.12.4) *)

  | red_spec_object_can_put_default : forall An S C l x o, (* Step 1 *)
      red_expr S C (spec_object_get_own_property l x (spec_object_can_put_1 l x)) o ->      
      red_expr S C (spec_object_can_put builtin_default_can_put l x) o  

  | red_spec_object_can_put_default_1_some : forall b An S C l x A o, (* Step 2 *)
      b = (If prop_attributes_is_accessor A then true else false) ->
      red_expr S C (spec_object_can_put_default_2 l x b) o ->
      red_expr S C (spec_object_can_put_default_1 l x (prop_descriptor_some A)) o

  | red_spec_object_can_put_default_2_some_accessor : forall b An S C l x A o, (* Step 2.a *)
      (b = If (prop_attributes_set A = None) then false else true) ->
      red_expr S C (spec_object_can_put_default_2 l x true) (out_ter S b)

  | red_spec_object_can_put_default_2_some_data : forall b S C l x A o, (* Step 2.b *)
      prop_attributes_is_data A ->
      b = unsome_default false (prop_attributes_writable A) -> 
      (* TODO: above could be [prop_attributes_writable A = Some b] if we know that data_descr implies writable field *)
      red_expr S C (spec_object_can_put_default_2 l x false) (out_ter S b)

  | red_spec_object_can_put_default_1_undef : forall S C l x o lproto, (* Step 3 *)
      object_proto S l lproto ->
      red_expr S C (spec_object_can_put_default_3 l x lproto) o ->
      red_expr S C (spec_object_can_put_default_1 l x prop_descriptor_undef) o

  | red_spec_object_can_put_default_3_null : forall S C l x o b, (* Step 4 *)
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_default_3 l x null) (out_ter S b)

  | red_spec_object_can_put_default_3_not_null : forall S C l x o lproto Anproto, (* Step 5 *)
      object_get_property S lproto x Anproto ->
      red_expr S C (spec_object_can_put_default_4 l Anproto) o ->
      red_expr S C (spec_object_can_put_default_3 l x lproto) o

  | red_spec_object_can_put_default_4_undef : forall S C l x o b, (* Step 6 *)
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_default_4 l prop_descriptor_undef) (out_ter S b)

  | red_spec_object_can_put_default_4_some_accessor : forall S C l A b, (* Step 7 *)
      prop_attributes_is_accessor A ->
      (b = If (prop_attributes_set A = None) then false else true) ->
      red_expr S C (spec_object_can_put_default_4 l (prop_descriptor_some A)) (out_ter S b)

  | red_spec_object_can_put_default_4_some_data : forall S C l x o A bext b, (* Step 8 *)
      prop_attributes_is_data A ->
      object_extensible S l bext ->
      b = (If bext = false
            then false
            else unsome_default false (prop_attributes_writable A)) ->
      (* TODO: here again, above could be enforcing [prop_attributes_writable A = Some b] *)
      red_expr S C (spec_object_can_put_default_4 l (prop_descriptor_some A)) (out_ter S b)

  (** Put (returns void) *)

  | red_spec_object_put : forall S C l x v throw o,
      object_method object_put_ S l B ->
      red_expr S C (spec_object_put_1 B l x v throw) o ->
      red_expr S C (spec_object_put l x v throw) o  

  (** Put, default  (8.12.5) *)

  | red_spec_object_put_default : forall o1 S C l x v throw o, (* Step 1 *)
      red_expr S C (spec_object_can_put_default l x) o1 ->
      red_expr S C (spec_object_put_default_1 l x v throw o1) o ->
      red_expr S C (spec_object_put_default builtin_default_put l x v throw) o  

  | red_spec_object_put_default_1_false : forall S C l x v throw o, (* Steps 1.a and 1.b *)
      red_expr S C (spec_error_or_void throw builtin_type_error) o ->
      red_expr S C (spec_object_put_default_1 l x v throw (out_ter S false)) o

  | red_spec_object_put_default_1_true : forall AnOwn S C l x v throw o, (* Step 2 *)
      red_expr S C (spec_object_get_own_property l x (spec_object_put_2 l x v throw)) o ->      
      red_expr S C (spec_object_put_1 l x v throw (out_ter S true)) o

  | red_spec_object_put_default_2_data : forall A' S C l x v throw AnOwn o1 o, (* Step 3 *)
      prop_descriptor_is_data AnOwn -> 
      A' = prop_attributes_create_value v ->
      red_expr S C (spec_object_define_own_prop l x A' throw) o1 ->
      red_expr S C (spec_object_put_default_return o1) o ->
      red_expr S C (spec_object_put_default_2 l x v throw AnOwn) o

  | red_spec_object_put_default_2_not_data : forall AnOwn An S C l x v throw o, (* Step 4 *)
      ~ prop_descriptor_is_data AnOwn ->
      object_get_property S (value_object l) x An ->
      red_expr S C (spec_object_put_default_3 l x v throw An) o ->
      red_expr S C (spec_object_put_default_2 l x v throw AnOwn) o

  | red_spec_object_put_default_3_accessor : forall (lfsetter:loc) S C l x v throw A o1 o, (* Step 5 *)
      prop_attributes_is_accessor A ->
      prop_attributes_set A = Some lfsetter ->
      red_expr S C (spec_call lfsetter l (v::nil)) o1 ->
      red_expr S C (spec_object_put_default_return o1) o ->
      red_expr S C (spec_object_put_default_3 l x v throw A) o

  | red_spec_object_put_default_3_not_accessor : forall A' S C l x v throw A o1 o, (* Step 6 *)
      ~ prop_attributes_is_accessor A ->
      A' = prop_attributes_create_data v true true true ->
      red_expr S C (spec_object_define_own_prop l x A' throw) o1 ->
      red_expr S C (spec_object_put_default_return o1) o ->
      red_expr S C (spec_object_put_default_3 l x v throw A) o

  | red_spec_can_put_default_return : forall S C rv, (* Steps 3.C and 7 *)
      red_expr S C (spec_object_put_default_return (out_ter S rv)) (out_ter_void S)

  (** Special Put method for primitive values : TODO *)

  (** Has property (returns bool) *)

  | red_spec_object_has_property : forall An S C l x b,
      object_get_property S (value_object l) x An ->
      b = (If An = prop_descriptor_undef then false else true) ->
      red_expr S C (spec_object_has_prop l x) (out_ter S b)

  (** Delete (returns bool) *)

  | red_spec_object_delete : forall An S C l x throw o, (* Step 1 *)
(*TODO: as red *)       object_get_own_property S l x An ->
      red_expr S C (spec_object_delete_1 l x throw An) o ->
      red_expr S C (spec_object_delete l x throw) o

  | red_spec_object_delete_1_undef : forall S C l x throw, (* Step 2 *)
      red_expr S C (spec_object_delete_1 l x throw prop_descriptor_undef) (out_ter S true)

  | red_spec_object_delete_1_some : forall b A S C l x throw o, (* Step 3 *)
      b = (If prop_attributes_configurable A = Some true then true else false) ->
      red_expr S C (spec_object_delete_2 l x throw b) o ->
      red_expr S C (spec_object_delete_1 l x throw (prop_descriptor_some A)) o

  | red_spec_object_delete_2_true : forall S C l x throw S', (* Steps 3.a and 3.b *)
      object_rem_property S l x S' ->
      red_expr S C (spec_object_delete_2 l x throw true) (out_ter S' true)

  | red_spec_object_delete_2_false : forall A S C l x throw, (* Steps 4 and 5 *)
      red_expr S C (spec_error_or_cst throw builtin_type_error false) o ->
      red_expr S C (spec_object_delete_2 l x throw false) o 

(*---end todo---*)
  (** Define own property (returns bool)  -- TODO: check everything  *)

(*---start todo---*)

  | red_spec_object_define_own_property : forall oldpd extensible S C l x newpf throw o,(* Steps 1, 2. *)
(*TODO: as red *)       object_get_own_property S l x oldpd ->
      object_extensible S l extensible ->
      red_expr S C (spec_object_define_own_prop_1 l x oldpd newpf throw extensible) o ->
      red_expr S C (spec_object_define_own_prop l x newpf throw) o

  | red_spec_object_define_own_prop_1_undef_false : forall S C l x newpf throw, (* Step 3. *)
      red_expr S C (spec_object_define_own_prop_1 l x prop_descriptor_undef newpf throw false) (out_reject S throw)

  | red_spec_object_define_own_prop_1_undef_true : forall A' S C l x newpf throw S', (* Step 4. *)
      A' = (If (prop_attributes_is_generic newpf \/ prop_attributes_is_data newpf)
        then prop_attributes_convert_to_data newpf
        else prop_attributes_convert_to_accessor newpf) ->
      object_set_property S l x A' S' ->
      red_expr S C (spec_object_define_own_prop_1 l x prop_descriptor_undef newpf throw true) (out_ter S' true)

  | red_spec_object_define_own_prop_1_includes : forall S C l x oldpf newpf throw, (* Step 6 (subsumes 5). *)
      prop_attributes_contains oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_1 l x (prop_descriptor_some oldpf) newpf throw true) (out_ter S true)

  | red_spec_object_define_own_prop_1_not_include : forall S C l x oldpf newpf throw o, (* Steps 6 else branch. *)
      ~ prop_attributes_contains oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_1 l x (prop_descriptor_some oldpf) newpf throw true) o

  | red_spec_object_define_own_prop_2_reject : forall S C l x oldpf newpf throw, (* Step 7. *)
      change_enumerable_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) (out_reject S throw)

  | red_spec_object_define_own_prop_2_not_reject : forall S C l x oldpf newpf throw o, (* Step 7 else branch. *)
      ~ change_enumerable_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_2 l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_3_generic : forall S C l x oldpf newpf throw o,(* Step 8. *)
      prop_attributes_is_generic newpf ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_3_a : forall S C l x oldpf newpf throw o,(* Step 9. *)
      (prop_attributes_is_data oldpf) <> (prop_attributes_is_data newpf) ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_4a_1 : forall S C l x oldpf newpf throw, (* Step 9a. *)
      prop_attributes_configurable oldpf = Some false ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) (out_reject S throw)

  | red_spec_object_define_own_prop_4a_2 : forall changedpf S' S C l x oldpf newpf throw o, (* Step 9b, 9c. *)
      changedpf = (If (prop_attributes_is_data oldpf)
        then prop_attributes_convert_to_accessor oldpf
        else prop_attributes_convert_to_data oldpf) ->
      object_set_property S l x changedpf S' ->
      red_expr S' C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4a l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_3_b : forall S C l x oldpf newpf throw o, (* Step 10. *)
      prop_attributes_is_data oldpf ->
      prop_attributes_is_data newpf ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_4b_1 : forall S C l x oldpf newpf throw, (* Step 10a. *)
      prop_attributes_configurable oldpf = Some false ->
      change_data_attributes_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) (out_reject S throw)

  | red_spec_object_define_own_prop_4b_2 : forall S C l x oldpf newpf throw o, (* Step 10a else branch. *)
      (   (   prop_attributes_configurable oldpf = Some false
           /\ ~ change_data_attributes_on_non_configurable oldpf newpf)
      \/ (prop_attributes_configurable oldpf = Some true)) ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4b l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_3_c : forall S C l x oldpf newpf throw o, (* Step 11. *)
      prop_attributes_is_accessor oldpf ->
      prop_attributes_is_accessor newpf ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_4c_1 : forall S C l x oldpf newpf throw, (* Step 11a. *)
      prop_attributes_configurable oldpf = Some false ->
      change_accessor_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) (out_reject S throw)

   | red_spec_object_define_own_prop_4c_2 : forall S C l x oldpf newpf throw o, (* Step 11a else branch. *)
      prop_attributes_configurable oldpf = Some false ->
      ~ change_accessor_on_non_configurable oldpf newpf ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) o ->
      red_expr S C (spec_object_define_own_prop_4c l x oldpf newpf throw) o

  | red_spec_object_define_own_prop_5 : forall changedpf S C l x oldpf newpf throw h', (* Step 12, 13. *)
      changedpf = prop_attributes_transfer oldpf newpf ->
      object_set_property S l x changedpf h' ->
      red_expr S C (spec_object_define_own_prop_5 l x oldpf newpf throw) (out_ter h' true)

(*---end todo---*)


  (** Conversion to default value (returns value) *)
(* TODO: rename defaultvalue into default_value *)

  | red_spec_to_default : forall S C l prefo pref o,
      pref = unsome_default preftype_number prefo ->
      (* TODO: unless O is a Date object (see 15.9.6), in which case pref should be preftype_string *)
      red_expr S C (spec_to_default_1 l pref (other_preftypes pref)) o ->
      red_expr S C (spec_to_default l prefo) o

  | red_spec_to_default_1 : forall S C l pref1 pref2 o,
      red_expr S C (spec_to_default_sub_1 l (method_of_preftype pref1) (spec_to_default_2 l pref2)) o ->
      red_expr S C (spec_to_default_1 l pref1 pref2) o

  | red_spec_to_default_2 : forall S C l pref2 o,
      red_expr S C (spec_to_default_sub_1 l (method_of_preftype pref2) spec_to_default_3) o ->
      red_expr S C (spec_to_default_2 l pref2) o

  | red_spec_to_default_3 : forall S C o,
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C spec_to_default_3 o

  | red_spec_to_default_sub_1 : forall o1 S C l x K o,
      red_expr S C (spec_object_get l x) o1 ->
      red_expr S C (spec_to_default_sub_2 l o1 K) o ->
      red_expr S C (spec_to_default_sub_1 l x K) o

  | red_spec_to_default_sub_2_not_callable : forall S0 S C l v K o,
      callable S v None ->
      red_expr S C K o ->
      red_expr S0 C (spec_to_default_sub_2 l (out_ter S v) K) o

  | red_spec_to_default_sub_2_callable : forall S C lfunc l v K o B o1,
      callable S v (Some B) ->
      v = value_object lfunc ->
      red_expr S C (spec_call B (Some lfunc) (Some l) nil) o1 ->
      red_expr S C (spec_to_default_sub_3 o1 (expr_basic K)) o ->
      red_expr S C (spec_to_default_sub_2 l (out_ter S v) K) o
      (* Note: the spec does not say to call [getValue] on the result of the method call *)

  | red_spec_to_default_sub_3_prim : forall S0 S C K w,
      red_expr S0 C (spec_to_default_sub_3 (out_ter S (value_prim w)) K) (out_ter S w)

  | red_spec_to_default_sub_3_object : forall S0 S C l K o,
      red_expr S C K o ->
      red_expr S0 C (spec_to_default_sub_3 (out_ter S (value_object l)) K) o

  (*------------------------------------------------------------*)
  (** ** Operations on references (8.7) *)

  (** Get value on a reference (returns value) *)

  | red_spec_ref_get_value_value : forall S C v, (* Step 1 *)
      red_expr S C (spec_get_value v) (out_ter S v)

  | red_spec_ref_get_value_ref_a : forall S C r o, (* Steps 2 and 3 *)
      ref_is_unresolvable r ->
      red_expr S C (spec_error builtin_ref_error) o ->
      red_expr S C (spec_get_value r) o

  | red_spec_ref_get_value_ref_b: forall ext_get v S C r o, (* Steps 2 and 4 *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ext_get = (If ref_has_primitive_base r
        then spec_object_get_special
        else spec_object_get) ->
      red_expr S C (ext_get v (ref_name r)) o ->
      red_expr S C (spec_get_value r) o

  | red_spec_ref_get_value_ref_c : forall L S C r o, (* Step 5. *)
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_get_binding_value L (ref_name r) (ref_strict r)) o ->
      red_expr S C (spec_get_value r) o

  (** Put value on a reference (returns void) *)

  | red_spec_ref_put_value_value : forall S C v vnew o, (* Step 1. *)
      red_expr S C (spec_error builtin_ref_error) o ->
      red_expr S C (spec_put_value v vnew) o 
    
  | red_spec_ref_put_value_ref_a_1 : forall S C r vnew , (* Steps 2 and 3a. *)
      ref_is_unresolvable r ->
      ref_strict r = true ->
      red_expr S C (spec_error builtin_ref_error) o ->
      red_expr S C (spec_put_value r vnew) o

  | red_spec_ref_put_value_ref_a_2 : forall o S C r vnew, (* Steps 2 and 3b. *)
      ref_is_unresolvable r ->
      ref_strict r = false ->
      red_expr S C (spec_object_put builtin_global (ref_name r) vnew throw_false) o ->
      red_expr S C (spec_put_value r vnew) o 

  | red_spec_ref_put_value_ref_b : forall v ext_put S C r vnew o, (* Step 4. *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ext_put = (If ref_has_primitive_base r
        then spec_object_put_special
        else spec_object_put) ->
      red_expr S C (ext_put v (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o
      
  | red_spec_ref_put_value_ref_c : forall L S C r vnew o, (* Step 5. *)     
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_set_mutable_binding L (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (ret_ref r) vnew) o  

  (** Auxiliary: [spec_expr_get_value] as a combination of [red_expr] and [get_value] *)

  | red_spec_expr_get_value : forall S C e o o1,
      red_expr S C e o1 ->
      red_expr S C (spec_expr_get_value_1 o1) o ->
      red_expr S C (spec_expr_get_value e) o

  | red_spec_expr_get_value_1 : forall S0 S C rv o,
      red_expr S C (spec_get_value rv) o ->
      red_expr S0 C (spec_expr_get_value_1 (out_ter S rv)) o

  (** Auxiliary: [spec_expr_get_value_conv] as a combination [spec_expr_get_value] and a conversion *)

  | red_spec_expr_get_value_conv : forall S C e K o o1,
      red_expr S C (spec_expr_get_value e) o1 -> 
      red_expr S C (spec_expr_get_value_conv_1 K o1) o -> 
      red_expr S C (spec_expr_get_value_conv K e) o

  | red_spec_expr_get_value_conv_1 : forall S0 S C K v o,
      red_expr S C (K v) o ->
      red_expr S0 C (spec_expr_get_value_conv_1 K (out_ter S v)) o

  (*------------------------------------------------------------*)
  (** ** Operations on environment records (10.2) *)

  (** Has binding (returns bool) *)

  | red_spec_env_record_has_binding : forall S C L x o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_has_binding_1 L x E) o ->
      red_expr S C (spec_env_record_has_binding L x) o

  | red_spec_env_record_has_binding_1_decl : forall S C L x D b,
      b = (If decl_env_record_indom D x then true else false) ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_decl D)) (out_ter S b)

  | red_spec_env_record_has_binding_1_object : forall S C L x l pt o,
      red_expr S C (spec_object_has_prop l x) o ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_object l pt)) o

  (** Create mutable binding (returns void) *)

  | red_spec_env_record_create_mutable_binding : forall S C L x deletable_opt deletable o E,
      deletable = unsome_default false deletable_opt ->
      env_record_binds S L E ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable E) o ->
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o

  | red_spec_env_record_create_mutable_binding_1_decl_indom : forall S C L x deletable D S',
      ~ decl_env_record_indom D x ->
      S' = env_record_write_decl_env S L x (mutability_of_bool deletable) undef ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_decl D)) (out_ter_void S')

  | red_spec_env_record_create_mutable_binding_1_object : forall o1 S C L x deletable l pt o,
      red_expr S C (spec_object_has_prop l x) o1 ->
      red_expr S C (spec_env_record_create_mutable_binding_2 L x deletable l o1) o ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_object l pt)) o

  | red_spec_env_record_create_mutable_binding_obj_2 : forall A S0 C L x deletable l S o1 o,
      A = prop_attributes_create_data undef true true deletable ->
      red_expr S C (spec_object_define_own_prop l x A throw_true) o1 ->
      red_expr S C (spec_env_record_create_mutable_binding_3 o1) o ->
      red_expr S0 C (spec_env_record_create_mutable_binding_2 L x deletable l (out_ter S false)) o

  | red_spec_env_record_create_mutable_binding_obj_3 : forall S0 S C rv,
      red_expr S0 C (spec_env_record_create_mutable_binding_3 (out_ter S rv)) (out_ter_void S)

  (** Set mutable binding (returns void) *)

  | red_spec_env_record_set_mutable_binding : forall S C L x v str o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str E) o ->
      red_expr S C (spec_env_record_set_mutable_binding L x v str) o

  | red_spec_env_record_set_mutable_binding_1_decl : forall v_old mu S C L x v str D K o,
      decl_env_record_binds D x mu v_old ->
      K = (If mutability_is_mutable mu
            then (let S' := env_record_write_decl_env S L x mu v in
                  spec_returns (out_ter_void S'))
            else (spec_error_or_void str builtin_type_error)) ->
      red_expr S C K o ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str (env_record_decl D)) o

  | red_spec_env_record_set_mutable_binding_1_object : forall S C L x v str l pt o,
      red_expr S C (spec_object_put l x v str) o ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str (env_record_object l pt)) o

  (** Get binding value (returns value) *)

  | red_spec_env_record_get_binding_value : forall E S C L x str o,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_get_binding_value_1 L x str E) o ->
      red_expr S C (spec_env_record_get_binding_value L x str) o

  | red_spec_env_record_get_binding_value_1_decl : forall mu v S C L x str D K o,
      decl_env_record_binds D x mu v -> 
      K = (If mu = mutability_uninitialized_immutable
              then (spec_error_or_cst str builtin_ref_error undef)
              else (out_ter S v)) ->
      red_expr S C K o ->
      red_expr S C (spec_env_record_get_binding_value_1 L x str (env_record_decl D)) o

  | red_spec_env_record_get_binding_value_1_object : forall o1 S C L x str l pt o,
      red_expr S C (spec_object_has_prop l x) o1 ->
      red_expr S C (spec_env_record_get_binding_value_2 x str l o1) o ->
      red_expr S C (spec_env_record_get_binding_value_1 L x str (env_record_object l pt)) o

  | red_spec_env_record_get_binding_value_2_false : forall S0 C x str l S o,
      red_expr S C (spec_error_or_cst str builtin_ref_error undef) o ->
      red_expr S0 C (spec_env_record_get_binding_value_2 x str l (out_ter S false)) o

  | red_spec_env_record_get_binding_value_obj_2_true : forall S0 C x str l S o,
      red_expr S C (spec_object_get l x) o ->
      red_expr S0 C (spec_env_record_get_binding_value_2 x str l (out_ter S true)) o

  (** Delete binding (returns bool) *)

  | red_spec_env_record_delete_binding : forall S C L x o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_delete_binding_1 L x E) o ->
      red_expr S C (spec_env_record_delete_binding L x) o

  | red_spec_env_record_delete_binding_1_decl_indom : forall mu v S C L x D S' b,
      decl_env_record_binds D x mu v ->
      (If mu = mutability_deletable
          then (S' = env_record_write S L (decl_env_record_rem D x) /\ b = true)
          else (S' = S /\ b = false)) ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl D)) (out_ter S' b)

  | red_spec_env_record_delete_binding_1_decl_not_indom : forall S C L x D,
      ~ decl_env_record_indom D x ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl D)) (out_ter S true)

  | red_spec_env_record_delete_binding_1_object : forall S C L x l pt o,
      red_expr S C (spec_object_delete l x throw_false) o ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_object l pt)) o

  (** Implicit this value (returns value) *)

  | red_spec_env_record_implicit_this_value : forall S C L o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_implicit_this_value_1 L E) o ->
      red_expr S C (spec_env_record_implicit_this_value L) o

  | red_spec_env_record_implicit_this_value_1_decl : forall S C L D,
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_decl D)) (out_ter S undef)

  | red_spec_env_record_implicit_this_value_1_object : forall S C L l (pt : bool) v,
      v = (if pt then l else undef) ->
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_object l pt)) (out_ter S v)

  (** Create immutable binding (returns void) *)

  | red_spec_env_record_create_immutable_binding : forall D S C L x S',
      env_record_binds S L (env_record_decl D) ->
      ~ decl_env_record_indom D x ->
      S' = env_record_write_decl_env S L x mutability_uninitialized_immutable undef ->
      red_expr S C (spec_env_record_create_immutable_binding L x) (out_ter_void S')

  (** Initialize immutable binding (returns void) *)

  | red_spec_env_record_initialize_immutable_binding : forall D v_old S C L x v S',
      env_record_binds S L (env_record_decl D) ->
      decl_env_record_binds D x mutability_uninitialized_immutable v_old -> (* Note: v_old is always undef here *)
      S' = env_record_write_decl_env S L x mutability_immutable v ->
      red_expr S C (spec_env_record_initialize_immutable_binding L x v) (out_ter_void S')

  (** Auxiliary: combination of create mutable binding and set mutable binding (returns void) *)

  | red_spec_env_record_create_set_mutable_binding : forall S C L x deletable_opt v str o o1,
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o1 ->
      red_expr S C (spec_env_record_create_set_mutable_binding_1 o1 L x v str) o ->
      red_expr S C (spec_env_record_create_set_mutable_binding L x deletable_opt v str) o

  | red_spec_env_record_create_set_mutable_binding_1 : forall S S0 C L x v str o,
      red_expr S C (spec_env_record_set_mutable_binding L x v str) o ->
      red_expr S0 C (spec_env_record_create_set_mutable_binding_1 (out_ter_void S) L x v str) o


  (*------------------------------------------------------------*)
  (** ** Operations on lexical environments *)

  (** Get identifier reference (10.2.2.1) *)

  | red_spec_lexical_env_get_identifier_ref_nil : forall S C x str r,
      r = ref_create_value undef x str ->
      red_expr S C (spec_lexical_env_get_identifier_ref nil x str) (out_ter S r)

  | red_spec_lexical_env_get_identifier_ref_cons : forall S C L lexs x str o,
      red_expr S C (spec_lexical_env_get_identifier_ref_1 L lexs x str) o ->
      red_expr S C (spec_lexical_env_get_identifier_ref (L::lexs) x str) o

  | red_spec_lexical_env_get_identifier_ref_cons_1 : forall o1 S C L lexs x str o,
      red_expr S C (spec_env_record_has_binding L x) o1 ->
      red_expr S C (spec_lexical_env_get_identifier_ref_2 L lexs x str o1) o ->
      red_expr S C (spec_lexical_env_get_identifier_ref_1 L lexs x str) o

  | red_spec_lexical_env_get_identifier_ref_cons_2_true : forall S0 C L lexs x str S r,
      r = ref_create_env_loc L x str ->
      red_expr S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x str (out_ter S true)) (out_ter S r)

  | red_spec_lexical_env_get_identifier_ref_cons_2_false : forall S0 C L lexs x str S o,
      red_expr S C (spec_lexical_env_get_identifier_ref lexs x str) o ->
      red_expr S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x str (out_ter S false)) o
     
  (*------------------------------------------------------------*)
  (** ** Operations on execution contexts and entering of function code (10.4) *)
      
(*---start todo---*)

(*--- TODO: check this section*)

  (** TODO : 10.4.2 Entering eval code *)    

  | red_spec_execution_ctx_eval_call : forall S C K bd o,
      red_expr S C (spec_execution_ctx_eval_call K bd) o  

  (** Function call *)

  | red_spec_execution_ctx_function_call_direct : forall bd str newthis S C K func this args o,
      object_code S func (Some bd) ->
      str = funcbody_is_strict bd ->
      (If (str = true) then newthis = this
      else If this = null \/ this = undef then newthis = builtin_global
      else If type_of this = type_object then newthis = this
      else False) (* ~ function_call_should_call_to_object this str *)
      ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args str (out_ter S newthis)) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  | red_spec_execution_ctx_function_call_convert : forall bd str o1 S C K func this args o,
      object_code S func (Some bd) ->
      str = funcbody_is_strict bd ->
      (~ (str = true) /\ this <> null /\ this <> undef /\ type_of this <> type_object) ->
      red_expr S C (spec_to_object this) o1 ->
      red_expr S C (spec_execution_ctx_function_call_1 K func args str o1) o ->
      red_expr S C (spec_execution_ctx_function_call K func this args) o

  | red_spec_execution_ctx_function_call_1 : forall scope bd S' lex' C' str o1 S0 C K func args S this o,
      object_scope S func (Some scope) ->
      object_code S func (Some bd) ->
      (lex', S') = lexical_env_alloc_decl S scope ->
      C' = execution_ctx_intro_same lex' this str ->
      red_expr S' C' (spec_execution_ctx_binding_instantiation (Some func) (funcbody_prog bd) args) o1 ->
      red_expr S' C' (spec_execution_ctx_function_call_2 K o1) o ->
      red_expr S0 C (spec_execution_ctx_function_call_1 K func args str (out_ter S this)) o 
      
  | red_spec_execution_ctx_function_call_2 : forall S0 S C K o,
      red_expr S C K o ->
      red_expr S0 C (spec_execution_ctx_function_call_2 K (out_ter_void S)) o

  (** Binding instantiation --- TODO: check this section *)
  
  
  (*------------------------------------------------------------*)
  (** ** Operations on functions *)

 (* todo: move spec_call and  spec_new here, and also spec_new_primitive *)

  (** Has Instance *)

  | red_spec_object_has_instance_prim : forall S C l w o,
      red_expr S C (spec_object_has_instance builtin_spec_op_function_has_instance l (value_prim w)) (out_ter S false)
  
  | red_spec_object_has_instance_object : forall o1 S C l lv o,
      red_expr S C (spec_object_get l "prototype") o1 ->
      red_expr S C (spec_object_has_instance_1 lv o1) o ->
      red_expr S C (spec_object_has_instance builtin_spec_op_function_has_instance l (value_object lv)) o
      
  | red_spec_object_has_instance_1_prim : forall S0 S C lv v o,
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S v)) o
      
  | red_spec_object_has_instance_1_false : forall S0 S C lv lo,
      object_proto S lv null ->     
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) (out_ter S false)
      
  | red_spec_object_has_instance_1_true : forall proto lo S0 S C lv,
      object_proto S lv (value_object proto) ->
      proto = lo ->     
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) (out_ter S true)
      
   | red_spec_object_has_instance_1 : forall proto lo S0 S C lv v o,
      object_proto S lv (value_object proto) ->
      proto <> lo ->     
      red_expr S C (spec_object_has_instance_1 proto (out_ter S (value_object lo))) o ->
      red_expr S0 C (spec_object_has_instance_1 lv (out_ter S (value_object lo))) o
  
  
  (* Auxiliary reductions form Binding instantiation *)
  
  (* Create bindings for formal parameters Step 4d. *)

  | red_spec_binding_instantiation_formal_params_empty : forall S C K args L o,  (* Loop ends in Step 4d *)  
      red_expr S C (K args L) o ->
      red_expr S C (spec_binding_instantiation_formal_params K args L nil) o

  | red_spec_binding_instantiation_formal_params_non_empty : forall o1 S C K args L argname names o, (* Steps 4d i - iii *)
      let v := hd undef args in
      red_expr S C (spec_env_record_has_binding L argname) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_1 K (tl args) L argname names v o1) o ->
      red_expr S C (spec_binding_instantiation_formal_params K args L (argname::names)) o

  | red_spec_binding_instantiation_formal_params_1_declared : forall S S0 C K args L argname names v o,  (* Step 4d iv *)
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L argname names v (out_ter_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L argname names v (out_ter S true)) o

  | red_spec_binding_instantiation_formal_params_1_not_declared : forall o1 S S0 C K args L argname names v o, (* Step 4d iv *)
      red_expr S C (spec_env_record_create_mutable_binding L argname None) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L argname names v o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L argname names v (out_ter S false)) o

  | red_spec_binding_instantiation_formal_params_2 : forall o1 S S0 C K args L argname names v o,  (* Step 4d v *)
      red_expr S C (spec_env_record_set_mutable_binding L argname v (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_3 K args L names o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_2 K args L argname names v (out_ter_void S)) o

  | red_spec_binding_instantiation_formal_params_3 : forall o1 S S0 C K args L names o, (* Step 4d loop *)
      red_expr S C (spec_binding_instantiation_formal_params K args L names) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_3 K args L names (out_ter_void S)) o
      
  (* Create bindings for function declarations Step 5 *)
  
  | red_spec_binding_instantiation_function_decls_nil : forall o1 L S0 S C K args bconfig o, (* Step 5b *)
      red_expr S C (K L) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L nil bconfig (out_ter_void S)) o

  | red_spec_binding_instantiation_function_decls_cons : forall o1 L S0 S C K args fd fds bconfig o, (* Step 5b *)
      let str := funcbody_is_strict (funcdecl_body fd) in
      red_expr S C (spec_creating_function_object (funcdecl_parameters fd) (funcdecl_body fd) (execution_ctx_variable_env C) str) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_1 K args L fd fds str bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L (fd::fds) bconfig (out_ter_void S)) o

  | red_spec_binding_instantiation_function_decls_1 : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5c *)
      red_expr S C (spec_env_record_has_binding L (funcdecl_name fd)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_1 K args L fd fds str bconfig (out_ter S fo)) o

  | red_spec_binding_instantiation_function_decls_2_false : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5d *)
      red_expr S C (spec_env_record_create_mutable_binding L (funcdecl_name fd) (Some bconfig)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig (out_ter S false)) o

  | red_spec_binding_instantiation_function_decls_2_true_global : forall A o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5e ii *)
      object_get_property S builtin_global (funcdecl_name fd) (prop_descriptor_some A) ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo A (prop_attributes_configurable A) bconfig) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args env_loc_global_env_record fd fds str fo bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_function_decls_3_true : forall o1 L S C K args fd fds str fo bconfig o, (* Step 5e iii *)
      let A := prop_attributes_create_data undef true true bconfig in
      red_expr S C (spec_object_define_own_prop builtin_global (funcdecl_name fd) A true) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds str fo bconfig o1) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo A (Some true) bconfig) o

  | red_spec_binding_instantiation_function_decls_3_false_type_error : forall o1 L S C K args fd fds str fo A configurable bconfig o, (* Step 5e iv *)
      configurable <> Some true ->
      prop_descriptor_is_accessor A \/ (prop_attributes_writable A <> Some true \/ prop_attributes_enumerable A <> Some true) ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo A configurable bconfig) (out_type_error S)

  | red_spec_binding_instantiation_function_decls_3_false : forall o1 L S C K args fd fds str fo A configurable bconfig o, (* Step 5e iv *)
     configurable <> Some true ->
      ~ (prop_descriptor_is_accessor A) /\ prop_attributes_writable A = Some true /\ prop_attributes_enumerable A = Some true ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds str fo bconfig (out_ter_void S)) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo A configurable bconfig) o

  | red_spec_binding_instantiation_function_decls_2_true : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5e *)
      L <> env_loc_global_env_record ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig (out_ter_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_function_decls_4 : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5f *)
      red_expr S C (spec_env_record_set_mutable_binding L (funcdecl_name fd) (value_object fo) str) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls K args L fds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig (out_ter_void S)) o
      
  (* Create bindings for variable declarations Step 8 *)
      
  | red_spec_binding_instantiation_var_decls_non_empty : forall o1 L S0 S C vd vds bconfig o, (* Step 8b *)
      red_expr S C (spec_env_record_has_binding L vd) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls_1 L vd vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls L (vd::vds) bconfig (out_ter_void S)) o

  | red_spec_binding_instantiation_var_decls_1_true : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig (out_ter_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_var_decls_1_false : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      red_expr S C (spec_env_record_create_set_mutable_binding L vd (Some bconfig) undef (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S false)) o

  | red_spec_binding_instantiation_var_decls_empty : forall o1 L S0 S C bconfig o, (* Step 8 *)
      red_expr S0 C (spec_binding_instantiation_var_decls L nil bconfig (out_ter_void S)) (out_ter_void S)     
      
  (* Declaration Binding Instantiation Main Part *)    

  | red_spec_execution_ctx_binding_instantiation : forall L tail S C func code args o, (* Step 1 *)
      (* todo: handle eval case -- step 2 *)
      (* todo: [code] needs to contain all the function declarations and the variable declarations *)

      execution_ctx_variable_env C = L :: tail ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 func code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation func code args) o
      (* Assumption made: if func is None, then code is global code or eval code, otherwise it is function code. 
         TODO: have an enumeration code_type? *)

  | red_spec_execution_ctx_binding_instantiation_1_function : forall names_option S C func code args L o, (* Step 4a *)
      object_formal_parameters S func names_option ->
      let names := unsome_default nil names_option in
      red_expr S C (spec_binding_instantiation_formal_params (spec_execution_ctx_binding_instantiation_2 code) args L names) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 (Some func) code args L) o

  | red_spec_execution_ctx_binding_instantiation_1_not_function : forall L S C code args o, (* Step 4 *)
      red_expr S C (spec_execution_ctx_binding_instantiation_2 code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 None code args L) o

  | red_spec_execution_ctx_binding_instantiation_function_2 : forall bconfig L S C code args o, (* Step 5 *)
      bconfig = false (* TODO: configurableBindings with eval *) ->
      let fds := prog_funcdecl code in
      red_expr S C (spec_binding_instantiation_function_decls (spec_execution_ctx_binding_instantiation_3 code bconfig) args L fds bconfig (out_ter_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 code args L) o

  (* TODO steps 6-7 *)

  | red_spec_execution_ctx_binding_instantiation_3 : forall o1 L S C code bconfig o, (* Step 8 *)
      let vds := prog_vardecl code in
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig (out_ter_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_3 code bconfig L) o
      
  (** Creating function object *)
    
  | red_spec_creating_function_object_proto : forall o1 S0 S C K l b o, 
      red_expr S C (spec_constructor_builtin builtin_object_new nil) o1 ->
      red_expr S C (spec_creating_function_object_proto_1 K l o1) o ->
      red_expr S0 C (spec_creating_function_object_proto K l (out_ter S b)) o
    
  | red_spec_creating_function_object_proto_1 : forall o1 S0 S C K l lproto b o, 
      let A := prop_attributes_create_data (value_object l) true false true in 
      red_expr S C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
      red_expr S C (spec_creating_function_object_proto_2 K l lproto o1) o ->
      red_expr S0 C (spec_creating_function_object_proto_1 K l (out_ter S lproto)) o
      
   | red_spec_creating_function_object_proto_2 : forall o1 S0 S C K l lproto b o, 
      let A := prop_attributes_create_data (value_object lproto) true false false in 
      red_expr S C (spec_object_define_own_prop l "prototype" A false) o1 ->
      red_expr S C (K o1) o ->
      red_expr S0 C (spec_creating_function_object_proto_2 K l lproto (out_ter S b)) o
  
  | red_spec_creating_function_object : forall l S' o1 S C names bd X str o,
      let O := object_new builtin_function_proto "Function" in
      let O1 := object_with_invokation O 
        (Some builtin_spec_op_function_constructor) 
        (Some builtin_spec_op_function_call) 
        (Some builtin_spec_op_function_has_instance) in
      let O2 := object_with_details O1 (Some X) (Some names) (Some bd) None None None None in
      (l, S') = object_alloc S O2 ->
      let A := prop_attributes_create_data (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_proto (spec_creating_function_object_1 str l) l o1) o ->
      red_expr S C (spec_creating_function_object names bd X str) o
                     


   | red_spec_creating_function_object_1_not_strict : forall o1 S0 S C l b, 
      red_expr S0 C (spec_creating_function_object_1 false l (out_ter S b)) (out_ter S l)
      
   | red_spec_creating_function_object_1_strict : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "caller" A false) o1 ->
      red_expr S C (spec_creating_function_object_2 l o1) o ->
      red_expr S0 C (spec_creating_function_object_1 true l (out_ter S b)) o
      
  | red_spec_creating_function_object_2 : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := prop_attributes_create_accessor vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "arguments" A false) o1 ->
      red_expr S C (spec_creating_function_object_3 l o1) o ->
      red_expr S0 C (spec_creating_function_object_2 l (out_ter S b)) o
      
  | red_spec_creating_function_object_3 : forall o1 S0 S C l b o, 
      red_expr S0 C (spec_creating_function_object_3 l (out_ter S b)) (out_ter S l)
      
  | red_spec_call_builtin: forall S C builtinid lo this args o,
      builtinid <> builtin_spec_op_function_call /\ builtinid <> builtin_spec_op_function_bind_call ->
      red_expr S C (spec_call_builtin builtinid args) o -> 
      red_expr S C (spec_call builtinid lo this args) o
      
  | red_spec_call_p: forall S C l this args o,
      red_expr S C (spec_op_function_call l this args) o -> 
      red_expr S C (spec_call builtin_spec_op_function_call (Some l) (Some this) args) o
      
  | red_spec_call_prog: forall S C l this args o,      
      red_expr S C (spec_execution_ctx_function_call (spec_op_function_call_1 l) l this args) o ->
      red_expr S C (spec_op_function_call l this args) o
      
  | red_spec_call_prog_1_empty: forall p o1 S C l o,
      (* TODO: check if red_prog return (normal, undef, empty) if function body is empty *)
      object_code S l None ->
      red_expr S C (spec_op_function_call_1 l) (out_ter S (res_normal undef))
      
  | red_spec_call_prog_1_prog: forall bd o1 S C l o,
      object_code S l (Some bd) ->
      red_prog S C (funcbody_prog bd) o1 ->
      red_expr S C (spec_op_function_call_2 o1) o ->
      red_expr S C (spec_op_function_call_1 l) o
      
  | red_spec_call_prog_2_throw: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_throw v))) (out_ter S (res_throw v))
      
  | red_spec_call_prog_2_return: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_return v))) (out_ter S (res_normal v))
      
  | red_spec_call_prog_2_normal: forall S C v,
      red_expr S C (spec_op_function_call_2 (out_ter S (res_normal v))) (out_ter S (res_normal undef))
      
  | red_spec_constructor_builtin: forall S C builtinid lo args o,
      builtinid <> builtin_spec_op_function_constructor /\ builtinid <> builtin_spec_op_function_bind_constructor ->
      red_expr S C (spec_constructor_builtin builtinid args) o -> 
      red_expr S C (spec_constructor builtinid lo args) o
      
  | red_spec_constructor_function: forall S C l args o,
      red_expr S C (spec_function_constructor l args) o -> 
      red_expr S C (spec_constructor builtin_spec_op_function_constructor (Some l) args) o
      
  | red_spec_function_constructor : forall o1 S C l args o,
      red_expr S C (spec_object_get (value_object l) "prototype") o1 ->
      red_expr S C (spec_function_constructor_1 l args o1) o ->
      red_expr S C (spec_function_constructor l args) o
      
  | red_spec_function_constructor_1 : forall l' vproto O S' builtinid o1 S0 S C l args v o,
      vproto = (If (type_of v) = type_object then v else builtin_object_proto) ->
      O = object_new vproto "Object" true ->
      (l', S') = object_alloc S O ->
      object_call S' l (Some builtinid) ->
      red_expr S' C (spec_call builtinid (Some l) (Some (value_object l')) args) o1 ->
      red_expr S' C (spec_function_constructor_2 l' o1) o ->
      red_expr S0 C (spec_function_constructor_1 l args (out_ter S v)) o
      
  | red_spec_function_constructor_2 : forall S0 S C l' v vr o,
      vr = (If (type_of v = type_object) then v else l') ->
      red_expr S0 C (spec_function_constructor_2 l' (out_ter S v)) (out_ter S vr)
      
(*      

      
      
      let A := prop_attributes_create_data (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_proto (spec_creating_function_object_1 str l) l o1) o ->
*)


  (** Shortcut: creates a new function object in the given execution context *)
  (* Daniele: [spec_creating_function_object] requires the function body as
     a string as the 2nd argument, but we don't have it. *)
  | red_spec_create_new_function_in : forall S C args bd o,
      red_expr S C (spec_creating_function_object args bd (execution_ctx_lexical_env C) (execution_ctx_strict C)) o ->
      red_expr S C (spec_create_new_function_in C args bd) o


     



(*---end todo---*)


(**************************************************************)
(** ** Reduction rules for builtin functions *)

(*------------------------------------------------------------*)
(** ** Global object builtin functions (15.1) *)

  (** Eval (returns value) *)  

  | red_spec_call_global_eval : forall S C args v o,
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_global_eval_1 v) o ->
      red_expr S C (spec_call_builtin builtin_global_eval args) o

  | red_spec_call_global_eval_1_not_string : forall S C v,
      type_of v <> type_string ->
      red_expr S C (spec_call_global_eval_1 v) (out_ter S v)  
      
  | red_spec_call_global_eval_1_string_not_parse : forall s S C o,
      parse_impossible s ->
      red_expr S C (spec_error builtin_syntax_error) o -> 
      red_expr S C (spec_call_global_eval_1 s) o 
      
  | red_spec_call_global_eval_1_string_parse : forall s p S C o,
      parse_successful s p ->
      red_expr S C (spec_execution_ctx_eval_call (spec_call_global_eval_1_2 p) (funcbody_intro p s)) o -> 
      (* TODO: check line above; in particular, does it have to be in CPS form? *)
      red_expr S C (spec_call_global_eval_1 s) o 
      
  | red_spec_call_global_eval_1_2 : forall o1 S C p o,
      red_prog S C p o1 ->
      red_expr S C (spec_call_global_eval_1_3 o1) o ->
      red_expr S C (spec_call_global_eval_1_2 p) o  
      
  | red_spec_call_global_eval_1_3_normal_value: forall S C v,
      red_expr S C (spec_call_global_eval_1_3 (out_ter S v)) (out_ter S v)
      
  | red_spec_call_global_eval_1_3_normal_empty: forall S C R labo,
      R = res_intro restype_normal resvalue_empty labo ->
      red_expr S C (spec_call_global_eval_1_3 (out_ter S R)) (out_ter S undef)
      
  | red_spec_call_global_eval_1_3_throw: forall S C R,
      res_type R = restype_throw ->
      red_expr S C (spec_call_global_eval_1_3 (out_ter S R)) (out_ter S (res_throw (res_value R)))     
     
  (** IsNan (returns bool) *)

  | red_spec_call_global_is_nan : forall S C v o o1 args, 
      arguments_from args (v::nil)  -> 
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_global_is_nan_1 o1) o ->
      red_expr S C (spec_call_builtin builtin_global_is_nan args) o

  | red_spec_call_global_is_nan_1 : forall S S0 C b n,
      b = (If n = JsNumber.nan then true else false) ->
      red_expr S0 C (spec_call_global_is_nan_1 (out_ter S n)) (out_ter S b)

  (** IsFinite (returns bool) *)

  | red_spec_call_global_is_finite : forall S C v o o1 args, 
      arguments_from args (v::nil)  ->
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_global_is_finite_1 o1) o ->
      red_expr S C (spec_call_builtin builtin_global_is_finite args) o

  | red_spec_call_global_is_finite_1 : forall S S0 C b n,
      b = (If (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity) then false else true) ->
      red_expr S0 C (spec_call_global_is_finite_1 (out_ter S n)) (out_ter S b)   
    

(*------------------------------------------------------------*)
(** ** Object builtin functions (15.2) *)

  (** Object([value]) (returns object_loc)  (15.2.1.1)  *)

  | red_spec_call_object_call : forall S C args v,
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_call_1 v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_call args) o

  | red_spec_call_object_call_1_null_or_undef : forall S C v o,
      (v = null \/ v = undef) ->
      red_expr S C (spec_call_object_new_1 v) o ->
      red_expr S C (spec_call_object_call_1 v) o

  | red_spec_call_object_call_1_other : forall S C v o,
      red_expr S C (spec_to_object v) o ->
      red_expr S C (spec_call_object_call_1 v) o

  (** new Object([value]) (returns object_loc)  (15.2.2.1) *)
  
  | red_spec_call_object_new : forall S C args v,
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_new_1 v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_new args) o
      
  | red_spec_call_object_new_1_object : forall S C v,
      type_of v = type_object ->
      red_expr S C (spec_call_object_new_1 v) (out_ter S v)

  | red_spec_call_object_new_1_prim : forall S C v T o,
      T = type_of v ->
      (T = type_string \/ T = type_bool \/ T = type_number) ->
      red_expr S C (spec_to_object v) o ->
      red_expr S C (spec_call_object_new_1 v) o
 
  | red_spec_call_object_new_1_null_or_undef : forall S C v O l S',
      (v = null \/ v = undef) ->
      O = object_new builtin_object_proto "Object" ->
      (l, S') = object_alloc S O ->
      red_expr S C (spec_call_object_new_1 v) (out_ter S' l)

  (** GetPrototypeOf (returns value)  (15.2.3.2) *)
  
  | red_spec_call_object_get_prototype_of : forall S C v r args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_get_prototype_of_1 v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_get_prototype_of args) o

  | red_spec_call_object_get_prototype_of_1_not_object : forall S C v o, 
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_object_get_prototype_of_1 v) o ->
          
  | red_spec_call_object_get_prototype_of_1_object : forall S C l v, 
      object_proto S l v ->
      red_expr S C (spec_call_object_get_prototype_of_1 l) (out_ter S v)

  
(*------------------------------------------------------------*)
(** ** Object prototype builtin functions (15.2.3) *)

  (** Object.prototype.toString() (returns string)  (15.2.4.2) *)

  | red_spec_call_object_proto_to_string : forall S C args o, 
      red_expr S C (spec_call_object_proto_to_string_1 (execution_ctx_this_binding C)) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_to_string args) o

  | red_spec_call_object_proto_to_string_1_undef : forall S C, 
      red_expr S C (spec_call_object_proto_to_string_1 undef) (out_ter S "[object Undefined]"%string)

  | red_spec_call_object_proto_to_string_1_null : forall S C, 
      red_expr S C (spec_call_object_proto_to_string_1 null) (out_ter S "[object Null]"%string)

  | red_spec_call_object_proto_to_string_1_other : forall S C v o o1, 
      ~ (v = null \/ v = undef) ->
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (spec_call_object_proto_to_string_2 o1) o ->
      red_expr S C (spec_call_object_proto_to_string_1 v) o

  | red_spec_call_object_proto_to_string_2 : forall S0 S C l s sclass,
      object_class S l sclass ->
      s = "[object " ++ sclass ++ "]" ->
      red_expr S0 C (spec_call_object_proto_to_string_2 (out_ter S l)) (out_ter S s)
 
  (** Object.prototype.valueOf() (returns value)  (15.2.4.4) *)

  | red_spec_call_object_proto_value_of : forall S C args o,   
      red_expr S C (spec_to_object (execution_ctx_this_binding C)) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_value_of args) o 

   (** Object.prototype.isPrototypeOf() (returns bool)  (15.2.4.6) *)

   | red_spec_call_object_proto_is_prototype_of_not_object : forall S C args v o, (* Step 0 *)
      arguments_from args (v::nil)  ->
      red_expr S C (spec_call_builtin spec_call_object_proto_is_prototype_of_2_1 v) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_is_prototype_of args) o

   | red_spec_call_object_proto_is_prototype_of_1_not_object : forall S C v, (* Step 1 *)
      type_of v <> type_object ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v) (out_ter S false)

   | red_spec_call_object_proto_is_prototype_of_1_object : forall S C l o1 o, (* Step 2 *)
      red_expr S C (spec_to_object (execution_ctx_this_binding C)) o1 ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_2 o1 l) o ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_1 l) o

   | red_spec_call_object_proto_is_prototype_of_2 : forall S0 S C l lthis o,
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l) o ->
      red_expr S0 C (spec_call_object_proto_is_prototype_of_2_2 (out_ter S lthis) l)) o

   | red_spec_call_object_proto_is_prototype_of_3 : forall S C l lthis vproto o, (* Step 3.a *)
      object_proto S l vproto -> 
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis vproto) o ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l)) o

   | red_spec_call_object_proto_is_prototype_of_4_null : forall S C lthis o, (* Step 3.b *)
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis null)) (out_ter S false)

   | red_spec_call_object_proto_is_prototype_of_4_equal : forall S C lthis o, (* Step 3.c *)
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis lthis)) (out_ter S true)
  
   | red_spec_call_object_proto_is_prototype_of_4_equal : forall S C l lthis lproto o, (* Look back to step 3 *)
      (* Note: we implicitly enforce the fact that a proto can only be a location or null *)
      lproto <> lthis -> 
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis lproto)) o ->
      red_expr S C ( lthis lproto)) o


  (*------------------------------------------------------------*)
  (** ** Boolean builtin functions *)

  (** Boolean(value)  (returns object_loc)  (15.6.1) *)

  | red_spec_call_bool_call : forall S C v o args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_to_boolean v) o ->
      red_expr S C (spec_call_builtin builtin_bool_call args) o 

  (** new Boolean(value)  (returns object_loc)  (15.6.2.1) *)
  
  | red_spec_bool_new : forall S C v o o1 args,
      arguments_from args (v::nil) -> 
      red_expr S C (spec_to_boolean v) o1 ->
      red_expr S C (spec_call_bool_new_1 o1) o ->
      red_expr S C (spec_constructor_builtin builtin_bool_new args) o
  
   | red_spec_bool_new_1 : forall O l b S' S C,
      let O1 := object_new builtin_bool_proto "Boolean" in 
      let O := object_with_primitive_value O1 b in 
      (l, S') = object_alloc S O ->
      red_expr S C (spec_call_bool_new_1 (out_ter S b)) (out_ter S' l) 


  (*------------------------------------------------------------*)
  (** ** Boolean prototype builtin functions *)

  (** Boolean.prototype.toString() (returns string)  (15.6.4.2) 
      Note: behavior encoded using valueOf and conversion to string *)

  | red_spec_call_bool_proto_to_string : forall S C args o1 o, 
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of args) o1 ->
      red_expr S C (spec_call_bool_proto_to_string_1 o1) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_to_string args) o

  | red_spec_call_bool_proto_to_string_1 : forall S0 S C s b, 
      s = (convert_bool_to_string b) ->
      red_expr S0 C (spec_call_bool_proto_to_string_1 (out_ter S b)) (out_ter S s)

  (** Boolean.prototype.valueOf() (returns bool)  (15.6.4.3) *)

  | red_spec_call_bool_proto_value_of : forall S C v o args, 
      v = execution_ctx_this_binding C ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of args) o

  | red_spec_call_bool_proto_value_of_1_bool : forall S C v b,
      value_viewable_as_prim "Boolean" S v b ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) (out_ter S b)

   | red_spec_call_bool_proto_value_of_1_not_bool : forall S C v o,
      (forall b, ~ value_viewable_as_prim "Boolean" S v b) ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) o


  (*------------------------------------------------------------*)
  (** ** Number builtin functions *)

  (** Number(value) (returns object_loc)  (15.7.1.1) *)

  | red_spec_call_number_call_nil : forall S C, 
      red_expr S C (spec_call_builtin builtin_number_call nil) (out_ter S JsNumber.zero) 

  | red_spec_call_number_call_not nil : forall S C v o args,
      args <> nil ->
      arguments_from args (v::nil) ->
      red_expr S C (spec_to_number v) o ->
      red_expr S C (spec_call_builtin builtin_number_call args) o 

  (** new Number([value]) (returns object_loc)  (15.7.2.1) *)
  
  | red_spec_call_number_new_nil : forall S C args,
      red_expr S C (spec_call_number_new_1 (out_ter S JsNumber.zero)) o ->
      red_expr S C (spec_constructor_builtin builtin_number_new nil) o

  | red_spec_call_number_new_not_nil: forall S C v o o1 args,
      args <> nil ->
      arguments_from args (v::nil) -> 
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_number_new_1 o1) o ->
      red_expr S C (spec_constructor_builtin builtin_number_new args) o
  
  | red_spec_call_number_new_1 : forall S0 S C S' O l v,
      let O1 := object_new builtin_number_proto "Number" in
      let O := object_with_primitive_value O1 v in 
      (l, S') = object_alloc S O ->
      red_expr S0 C (spec_call_number_new_1 (out_ter S v)) (out_ter S' l) 


  (*------------------------------------------------------------*)
  (** ** Number prototype builtin functions *)

  (* Number.prototype.toString() : LATER (see bottom of this file) *)

  (* Number.prototype.valueOf() (returns number)  (15.7.4.4) *)

  | red_spec_call_number_proto_value_of : forall S C o v args, 
      v = execution_ctx_this_binding C ->
      red_expr S C (spec_call_number_proto_value_of_1 v) o ->
      red_expr S C (spec_call_builtin builtin_number_proto_value_of args) o

  | red_spec_call_number_proto_value_of_1_number : forall S C v n,
      value_viewable_as_prim "Number" S v n ->
      red_expr S C (spec_call_number_proto_value_of_1 v) (out_ter S n)

   | red_spec_call_number_proto_value_of_1_not_number : forall S C v o,
      (forall n, ~ value_viewable_as_prim "Number" S v n) ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_number_proto_value_of_1 v) o

  (*------------------------------------------------------------*)
  (** ** Error builtin functions *)
  
  (* TODO: spec_error *)

  (* TODO: call error new *)

  (* TODO: call error call *)

  (*------------------------------------------------------------*)
  (** ** Error prototype builtin functions *)
  
  (** Error.prototype.toString()  (15.11.4.4)  : LATER *)

  (** Error.prototype.valueOf()  : TODO: it's not in the spec! *)

  
.





(*******************************************************************************)
(*******************************************************************************)
(***************************** LATER *******************************************)
(*******************************************************************************)

(*----TODO: (arthur)

  (* 15.7.4.2: Number.prototype.toString([radix]) *)

  (* Daniele: I guess we don't have the algorithm for representing numbers 
     as strings with different radix. I'll just ignore this (i.e. always do
     toString in base 10) *)

  (* Daniele: I'm not convinced by this one :/ *)
  
  (* if [this] is not a number then throw Type Error exception *)
  | red_spec_call_number_proto_to_string_not_number : forall S C s b o v args, 
      v = execution_ctx_this_binding C ->
      not (type_of v = type_number) -> (* Daniele: check last lines of [15.7.4.2]. *)
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string args) o

  (* if [this] is a number we proceed to the next stages *)
  | red_spec_call_number_proto_to_string_number : forall S C s b o v args, 
      v = execution_ctx_this_binding C ->
      type_of v = type_number -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string args) o

  (* The [radix] parameter is not there: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_1_no_radix : forall S C v o args, 
      args = nil ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o 

  (* The [radix] parameter is undefined: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_1_undef_radix : forall S C v vr args o, 
      arguments_from args (vr::nil) ->
      vr = undef ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o 

  (* TODO: factorize the previous 2? *)

  (* The [radix] is present *)
  | red_spec_call_number_proto_to_string_number_1_radix : forall S C v vr args o o1,
      arguments_from args (vr::nil) ->
      not (vr = undef) ->
      red_expr S C (spec_to_integer vr) o1 ->
      red_expr S C (spec_call_number_proto_to_string_2 v o1) o -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o 
 
  (* If the [radix] is 10 we do a simple toString *)
  | red_spec_call_number_proto_to_string_2_radix_10 :forall S S' C v vr o,
      vr = value_prim (prim_number (JsNumber.of_int 10)) -> 
      red_expr S C (spec_to_string v) o ->
      red_expr S C (spec_call_number_proto_to_string_2 v (out_ter S' vr)) o
      
  (* If the [radix] is out of range we throw a Range Error exception *)
  | red_spec_call_number_proto_to_string_2_radix_out_of_range : forall S S' C v vr k o,
      vr = value_prim (prim_number (JsNumber.of_int k)) ->
      (k < 2 /\ k > 36) -> 
      red_expr S C (spec_error builtin_type_error) o -> (* Should be Range Error instead of Type Error *)
      red_expr S C (spec_call_number_proto_to_string_2 v (out_ter S' vr)) o
  
  (* If the [radix] is in range we do a simple toString 
     TODO: in fact the number should be printed using that radix
     implementation dependent) *)
  | red_spec_call_number_proto_to_string_2_radix_in_range : forall S S' C v vr k o,
      vr = value_prim (prim_number (JsNumber.of_int k)) ->
      not (k < 2 /\ k > 36) -> 
      red_expr S C (spec_to_string v) o -> (* This should be something different *)
      red_expr S C (spec_call_number_proto_to_string_2 v (out_ter S' vr)) o



  (** Throw Type Error Function Object Initialisation *)           
  
  (* Could we have this not a a reduction, but as simple function in JsInit? *)
  | red_spec_error_type_error : forall O O1 code O2 S' A o1 S C o,
      O = object_new builtin_function_proto "Function" ->
      O1 = object_with_invokation O None (Some builtin_spec_op_function_call) None ->
      (* TODO : Is this ok? TODO: make it compile*)
      (* code = funcbody_intro (prog_stat (stat_throw (expr_new (expr_identifier "TypeError") nil))) "throw TypeError()" -> 
      *)
      O2 = object_with_details O1 (Some (env_loc_global_env_record::nil)) (Some nil) (Some code) None None None None ->
      S' = object_write S builtin_function_throw_type_error O2 ->
      A = prop_attributes_create_data JsNumber.zero false false false ->
      red_expr S' C (spec_object_define_own_prop builtin_function_throw_type_error "length" A false) o1 ->
      red_expr S C (spec_error builtin_type_error_1 o1) o ->
      red_expr S C (spec_error builtin_type_error) o
  
  | red_spec_error_type_error_1 : forall O S' S0 S C v o,
      object_binds S builtin_function_throw_type_error O ->
      S' = object_write S builtin_function_throw_type_error (object_set_extensible_false O) ->
      red_expr S0 C (spec_error builtin_type_error_1 (out_ter S v)) (out_ter_void S')



------*)


(**------ begin under dvpt --------

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
      red_stat S0 C (stat_for_in_7 e1 t l vret lhdRef initProps visitedProps (out_ter_void S)) o


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
      (* TODO: use instead the res_type projection *)
      ~ (is_res_break res) /\ ~ (is_res_continue res) /\ ~ (is_res_normal res) ->

      red_stat S C (stat_for_in_9 e1 t l vret lhdRef initProps visitedProps res) (out_ter S res)

  | red_stat_for_in_6g_continue : forall o1 S C e1 t l vret lhdRef initProps visitedProps res o,
     (* TODO: check continue label is in current label set *)
      ~ (is_res_break res) /\ ((is_res_continue res) \/ (is_res_normal res)) ->
      red_stat S C (stat_for_in_4 e1 t l vret lhdRef initProps visitedProps) o ->
      red_stat S C (stat_for_in_9 e1 t l vret lhdRef initProps visitedProps res) o  

-- end todo *) 

(**------ end under dvpt --------*)

*)