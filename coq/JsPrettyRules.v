Require Import JsPreliminary JsPreliminaryAux JsPrettyInterm JsPrettyIntermAux JsInit.

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
(** ** Reduction rules for global code (??) *)

Inductive red_javascript : prog -> out -> Prop :=

  | red_javascript_intro : forall S S' C0 C p o,
      S = state_initial ->
      C0 = execution_ctx_initial (prog_intro_strictness p) ->
      red_expr S C (spec_execution_ctx_binding_instantiation codetype_global None p nil) (out_void S') ->
      red_prog S' C p o ->
      red_javascript p o


(**************************************************************)
(** ** Reduction rules for programs (14) *)

with red_prog : state -> execution_ctx -> ext_prog -> out -> Prop :=

  (** Abort rule for programs *)

  | red_prog_abort : forall S C extp o,
      out_of_ext_prog extp = Some o ->
      abort o ->
      ~ abort_intercepted_prog extp ->
      red_prog S C extp o

  (** Program  (10.4.1) *)

  | red_prog_prog : forall S C str els o,
      red_prog S C (prog_1 resvalue_empty els) o ->
      red_prog S C (prog_intro str els) o

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
      out_of_ext_stat extt = Some o ->
      abort o ->
      ~ abort_intercepted_stat extt ->
      red_stat S C extt o

  (** Block statement (recall [abort_intercepted_stat]) *)

  | red_stat_block : forall S C ts o,
      red_stat S C (stat_block_1 resvalue_empty ts) o ->
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
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_boolean 
                      (fun v => stat_if_1 v t2 t3opt)) o ->
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

  | red_stat_do_while_2_true : forall rv o1 S0 S C labs t1 e2 rv_old R o,
      rv = (If res_value R = resvalue_empty then rv_old else res_value R) ->
      red_stat S C (stat_do_while_3 labs t1 e2 rv R) o ->
      red_stat S0 C (stat_do_while_2 labs t1 e2 rv_old (out_ter S R)) o 

  (* TODO: update these rules following "while" rules after we approve them *)
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
      red_stat S C (stat_do_while_5 labs t1 e2 rv false) (out_ter S rv)

  | red_stat_do_while_5_true : forall S C labs t1 e2 rv o,
      red_stat S C (stat_do_while_1 labs t1 e2 rv) o ->
      red_stat S C (stat_do_while_5 labs t1 e2 rv true) o

  (** While statement (recall [abort_intercepted_stat]) *)

  | red_stat_while : forall S C labs e1 t2 o,
      red_stat S C (stat_while_1 labs e1 t2 resvalue_empty) o ->
      red_stat S C (stat_while labs e1 t2) o

  | red_stat_while_1 : forall S C labs e1 t2 rv o,
      red_stat S C (spec_expr_get_value_conv_stat e1 spec_to_boolean (stat_while_2 labs e1 t2 rv)) o ->
      red_stat S C (stat_while_1 labs e1 t2 rv) o

  | red_stat_while_2_false : forall S C labs e1 t2 rv,
      red_stat S C (stat_while_2 labs e1 t2 rv false) (out_ter S rv)

  | red_stat_while_2_true : forall S C labs e1 t2 rv o1 o,
      red_stat S C t2 o1 ->
      red_stat S C (stat_while_3 labs e1 t2 rv o1) o ->
      red_stat S C (stat_while_2 labs e1 t2 rv true) o

  | red_stat_while_3_true : forall rv S0 S C labs e1 t2 rv_old R o,
      rv = (If res_value R = resvalue_empty then rv_old else res_value R) ->
      red_stat S C (stat_while_4 labs e1 t2 rv R) o ->
      red_stat S0 C (stat_while_3 labs e1 t2 rv_old (out_ter S R)) o 

  | red_stat_while_4_break : forall S0 S C labs e1 t2 rv R,
      (res_type R = restype_break /\ res_label_in R labs) ->
      red_stat S C (stat_while_4 labs e1 t2 rv R) (out_ter S rv)

  | red_stat_while_4_continue : forall S0 S C labs e1 t2 rv R o,
      (   (res_type R = restype_continue /\ res_label_in R labs)
        \/ res_type R = restype_normal) ->
      red_stat S C (stat_while_1 labs e1 t2 rv) o ->      
      red_stat S C (stat_while_4 labs e1 t2 rv R) o

  | red_stat_while_4_abrupt : forall S0 S C labs e1 t2 rv R,
      abrupt_res R -> 
      ~ (res_type R = restype_break /\ res_label_in R labs) ->
      ~ (res_type R = restype_continue /\ res_label_in R labs) ->
      red_stat S C (stat_while_4 labs e1 t2 rv R) (out_ter S R)

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

  | red_stat_label : forall S C slab t o1 o,
      red_stat S C t o1 ->
      red_stat S C (stat_label_1 (label_string slab) o1) o ->
      red_stat S C (stat_label slab t) o

  | red_stat_label_1_normal : forall S0 S lab C rv,
      red_stat S0 C (stat_label_1 lab (out_ter S rv)) (out_ter S rv)

  | red_stat_label_1_break_eq : forall S0 S C R rv lab,
      R = res_intro restype_break rv lab ->
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

  | red_stat_try_1_throw_no_catch : forall S0 S C R fo o,
      res_type R = restype_throw ->
      red_stat S0 C (stat_try_4 R fo) o ->
      red_stat S0 C (stat_try_1 (out_ter S R) None fo) o

  | red_stat_try_1_throw_catch : forall v S0 S S' C lex lex' oldlex L x R t1 fo o1 o,
      res_type R = restype_throw ->
      lex = execution_ctx_lexical_env C ->
      (lex',S') = lexical_env_alloc_decl S lex ->
      lex' = L::oldlex -> (* Note: oldlex is in fact equal to lex *)
      (* TODO : Can the res_value R be empty value or reference value? 
                We need to change the type of create/set mutable binding then *)
      res_value R = resvalue_value v ->
      red_expr S' C (spec_env_record_create_set_mutable_binding L x None v throw_irrelevant) o1 ->
      red_stat S' C (stat_try_2 o1 lex' t1 fo) o -> (* [stat_try_2] is marked as intercepting [abort] rules in [abort_intercepted_stat]:  does that mean that there actually is a way not to execute the [finally] part of a [try/catch/finally] while actually executing a part of the [try] block?  -- Martin. *)
      red_stat S0 C (stat_try_1 (out_ter S R) (Some (x,t1)) fo) o

  | red_stat_try_2_catch : forall C S0 S lex' t1 fo o o1,
      red_stat S (execution_ctx_with_lex C lex') t1 o1 ->
      red_stat S C (stat_try_3 o1 fo) o ->
      red_stat S0 C (stat_try_2 (out_void S) lex' t1 fo) o

  | red_stat_try_3_catch_result : forall S0 S C R fo o,
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
      red_expr S C (expr_object_0 o1 pds) o ->
      red_expr S C (expr_object pds) o

  | red_expr_object_0 : forall S0 S C l pds o,
      red_expr S C (expr_object_1 l pds) o ->
      red_expr S0 C (expr_object_0 (out_ter S l) pds) o

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
      A = attributes_data_intro v true true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_val l x (out_ter S v) pds) o
  
  | red_expr_object_2_get : forall S C bd l x o o1 pds,
      red_expr S C (spec_create_new_function_in C nil bd) o1 ->
      red_expr S C (expr_object_3_get l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_get bd) pds) o
  
  | red_expr_object_3_get : forall S S0 C A l x v pds o,  
      A = attributes_accessor_intro undef v true true ->
      red_expr S C (expr_object_4 l x A pds) o ->
      red_expr S0 C (expr_object_3_get l x (out_ter S v) pds) o

  | red_expr_object_2_set : forall S S0 C A l x v pds o o1 bd args,
      red_expr S C (spec_create_new_function_in C args bd) o1 ->
      red_expr S C (expr_object_3_set l x o1 pds) o ->
      red_expr S C (expr_object_2 l x (propbody_set args bd) pds) o

  | red_expr_object_3_set : forall S S0 C A l x v pds o,
      A = attributes_accessor_intro v undef true true ->
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
      red_expr S0 C (expr_access_3 v1 (out_void S) v2) o

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
      red_expr S C (expr_call_3 (resvalue_ref r) (value_object l) vs) o
      
  | red_expr_call_3_env : forall L o1 S C o r l vs,
      (is_callable S l) ->
      ref_is_env_record r L -> 
      red_expr S C (spec_env_record_implicit_this_value L) o1 -> 
      red_expr S C (expr_call_4 l vs o1) o ->
      red_expr S C (expr_call_3 (resvalue_ref r) (value_object l) vs) o

  | red_expr_call_3_not_ref : forall S C v l vs o,
      red_expr S C (expr_call_4 l vs (out_ter S undef)) o ->
      red_expr S C (expr_call_3 (resvalue_value v) (value_object l) vs) o
   
  | red_expr_call_4 : forall S0 S C l vs v o,
      red_expr S C (spec_call l v vs) o ->
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
      red_expr S0 C (expr_function_1 s args bd L scope (out_void S)) o
      
  | red_expr_function_named_2 : forall o1 S0 S C s L l o,
      red_expr S C (spec_env_record_initialize_immutable_binding L s l) o1 ->
      red_expr S C (expr_function_3 l o1) o ->
      red_expr S0 C (expr_function_2 s L (out_ter S l)) o  
      
  | red_expr_function_named_3 : forall S0 S C l,
      red_expr S0 C (expr_function_3 l (out_void S)) (out_ter S l) 

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
      red_expr S0 C (expr_prepost_4 v (out_void S)) (out_ter S v)

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

  | red_expr_delete_1_ref_unresolvable : forall S0 S C r,
      ref_is_unresolvable r ->
      red_expr S0 C (expr_delete_1 (out_ter S r)) (out_ter S true)

  | red_expr_delete_1_ref_property : forall S0 S C r v o1 o,
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (expr_delete_2 r o1) o ->
      red_expr S0 C (expr_delete_1 (out_ter S r)) o

  | red_expr_delete_2 : forall S0 S C r l o,
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

  | red_expr_typeof_1_ref_resolvable : forall S0 S C r o1 o,
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
      red_expr S C (spec_object_default_value l prefo) o ->
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

  | red_spec_to_uint32_1 : forall S0 S C n K o,
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

  | red_spec_to_object_prim : forall S C w o v,
      ~ (v = prim_undef \/ v = prim_null) ->
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
      red_expr S C (spec_check_object_coercible v) (out_void S)

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
  (** ** Dispatch for operations on objects *)

  (** GetOwnProperty (passes a fully-populated property descriptor to the continuation) *)

  | red_spec_object_get_own_prop : forall S C l x K B o,
      object_method object_get_own_prop_ S l B ->
      red_expr S C (spec_object_get_own_prop_1 B l x K) o ->
      red_expr S C (spec_object_get_own_prop l x K) o  

  (** GetProperty (passes a fully-populated property descriptor to the continuation)  *)

  | red_spec_object_get_prop : forall S C l x K B o,
      object_method object_get_prop_ S l B ->
      red_expr S C (spec_object_get_prop_1 B l x K) o ->
      red_expr S C (spec_object_get_prop l x K) o  

  (** Get (returns value) *)

  | red_spec_object_get : forall S C l x B o,
      object_method object_get_ S l B ->
      red_expr S C (spec_object_get_1 B l l x) o ->
      red_expr S C (spec_object_get l x) o  

  (** CanPut (returns bool) *)

  | red_spec_object_can_put : forall S C l x B o,
      object_method object_can_put_ S l B ->
      red_expr S C (spec_object_can_put_1 B l x) o ->
      red_expr S C (spec_object_can_put l x) o  

  (** Put (returns void) *)

  | red_spec_object_put : forall S C l x v throw B o,
      object_method object_put_ S l B ->
      (* TODO: Daiva: Double check [this] value *)
      red_expr S C (spec_object_put_1 B l l x v throw) o ->
      red_expr S C (spec_object_put l x v throw) o

  (** HasProperty (returns bool) *)

  | red_spec_object_has_prop : forall S C l x B o,
      object_method object_has_prop_ S l B ->
      red_expr S C (spec_object_has_prop_1 B l x) o ->
      red_expr S C (spec_object_has_prop l x) o

  (** Delete (returns bool) *)

  | red_spec_object_delete : forall S C l x throw B o,
      object_method object_delete_ S l B ->
      red_expr S C (spec_object_delete_1 B l x throw) o ->
      red_expr S C (spec_object_delete l x throw) o

  (** DefaultValue (returns value) *)

  | red_spec_object_default_value : forall S C l prefo B o,
      object_method object_default_value_ S l B ->
      red_expr S C (spec_object_default_value_1 B l prefo) o ->
      red_expr S C (spec_object_default_value l prefo) o

  (** DefineOwnProperty (returns bool) *)

  | red_spec_object_define_own_prop : forall S C l x Desc throw B o,
      object_method object_define_own_prop_ S l B ->
      red_expr S C (spec_object_define_own_prop_1 B l x Desc throw) o ->
      red_expr S C (spec_object_define_own_prop l x Desc throw) o


  (*------------------------------------------------------------*)
  (** ** Default implementations for operations on objects (8.12) *)

  (** GetOwnProperty  (8.12.1) *)

  | red_spec_object_get_own_prop_1_default : forall S C l x K P Ao o, (* Beginning of steps 1 and 3 *)
      object_properties S l P -> (* TODO: combine this line and the next one using an auxiliary def *)
      Ao = Heap.read_option P x ->
      red_expr S C (spec_object_get_own_prop_2 l x K Ao) o ->
      red_expr S C (spec_object_get_own_prop_1 builtin_default_get_own_prop l x K) o  

  | red_spec_object_get_own_prop_2_none : forall S C l x K o, (* Step 1 *)
      red_expr S C (K full_descriptor_undef) o ->
      red_expr S C (spec_object_get_own_prop_2 l x K None) o  

  | red_spec_object_get_own_prop_2_some_data : forall S C l x K A o, (* Step 2 through 8 *)
      red_expr S C (K (full_descriptor_some A)) o ->  
      red_expr S C (spec_object_get_own_prop_2 l x K (Some A)) o  

  (** GetProperty  (8.12.2) *)

  | red_spec_object_get_prop_1_default : forall S C l x K o, (* Step 1 *)
      red_expr S C (spec_object_get_own_prop l x (spec_object_get_prop_2 l x K)) o ->
      red_expr S C (spec_object_get_prop_1 builtin_default_get_prop l x K) o  

  | red_spec_object_get_prop_2_not_undef : forall S C l x K A o, (* Step 2 *)
      red_expr S C (K (full_descriptor_some A)) o ->
      red_expr S C (spec_object_get_prop_2 l x K (full_descriptor_some A)) o  

  | red_spec_object_get_prop_2_undef : forall S C l x K vproto o, (* Step 3 *)
      object_proto S l vproto ->
      red_expr S C (spec_object_get_prop_3 l x K vproto) o ->
      red_expr S C (spec_object_get_prop_2 l x K full_descriptor_undef) o  

  | red_spec_object_get_prop_3_null : forall S C l x K o, (* Step 4 *)
      red_expr S C (K full_descriptor_undef) o ->
      red_expr S C (spec_object_get_prop_3 l x K null) o  

  | red_spec_object_get_prop_3_not_null : forall S C l x K lproto o, (* Step 5 *)
      red_expr S C (spec_object_get_prop lproto x K) o ->
      red_expr S C (spec_object_get_prop_3 l x K lproto) o  
  
  (** Get  (8.12.3) and (8.7.1)
      Note: rules are generalized so as to also handle the Put method on primitive values *)
  (* TODO: Maybe it'd be bettter not to factorize the two sets of rules...
           but copy-pasting is really ugly though.. *)

  | red_spec_object_get_1_default : forall S C vthis l x o, (* Step 1 *)
      red_expr S C (spec_object_get_prop l x (spec_object_get_2 vthis l)) o ->      
      red_expr S C (spec_object_get_1 builtin_default_get vthis l x) o  

  | red_spec_object_get_2_undef : forall S C vthis l, (* Step 2 *)
      red_expr S C (spec_object_get_2 vthis l full_descriptor_undef) (out_ter S undef)

  | red_spec_object_get_2_data : forall S C vthis l Ad v, (* Step 3 *)
      v = attributes_data_value Ad ->
      red_expr S C (spec_object_get_2 vthis l (attributes_data_of Ad)) (out_ter S v)

  | red_spec_object_get_2_accessor : forall S C vthis l Aa o, (* Step 4 *)
      red_expr S C (spec_object_get_3 vthis l (attributes_accessor_get Aa)) o ->
      red_expr S C (spec_object_get_2 vthis l (attributes_accessor_of Aa)) o

  | red_spec_object_get_3_accessor_undef : forall S C vthis l, (* Step 5 *)
      red_expr S C (spec_object_get_3 vthis l undef) (out_ter S undef) 

  | red_spec_object_get_3_accessor_object : forall B S C (lthis : object_loc) l lf o, (* Step 6 *)
      (* I changed this rule as a term [vthis] of type [object_loc] appeared in it, which strongly looked as an error.  Please check it.  -- Martin. *)
      red_expr S C (spec_call lf lthis nil) o ->
      red_expr S C (spec_object_get_3 lthis l lf) o
      
  (** CanPut  (8.12.4) *)

  | red_spec_object_can_put_1_default : forall S C l x o, (* Step 1 *)
      red_expr S C (spec_object_get_own_prop l x (spec_object_can_put_2 l x)) o ->      
      red_expr S C (spec_object_can_put_1 builtin_default_can_put l x) o  

  | red_spec_object_can_put_2_accessor : forall S C l x Aa b, (* Steps 2 and 2.a *)
      b = (If attributes_accessor_set Aa = undef then false else true) ->
      red_expr S C (spec_object_can_put_2 l x (attributes_accessor_of Aa)) (out_ter S b)

  | red_spec_object_can_put_2_data : forall S C l x Ad b, (* Step 2.b *)
      b = attributes_data_writable Ad ->
      red_expr S C (spec_object_can_put_2 l x (attributes_data_of Ad)) (out_ter S b)

  | red_spec_object_can_put_2_undef : forall S C l x o lproto, (* Step 3 *)
      object_proto S l lproto ->
      red_expr S C (spec_object_can_put_4 l x lproto) o ->
      red_expr S C (spec_object_can_put_2 l x full_descriptor_undef) o

  | red_spec_object_can_put_4_null : forall S C l x o b, (* Step 4 *)
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_4 l x null) (out_ter S b)

  | red_spec_object_can_put_4_not_null : forall S C l x o lproto, (* Step 5 *)
      red_expr S C (spec_object_get_prop lproto x (spec_object_can_put_5 l)) o ->
      red_expr S C (spec_object_can_put_4 l x lproto) o

  | red_spec_object_can_put_5_undef : forall S C l x o b, (* Step 6 *)
      object_extensible S l b ->
      red_expr S C (spec_object_can_put_5 l full_descriptor_undef) (out_ter S b)

  | red_spec_object_can_put_5_accessor : forall S C l Aa b, (* Step 7 *)
      b = (If attributes_accessor_set Aa = undef then false else true) ->
      red_expr S C (spec_object_can_put_5 l (attributes_accessor_of Aa)) (out_ter S b)

  | red_spec_object_can_put_5_data : forall S C l x Ad bext o, (* Step 8 *)
      object_extensible S l bext ->
      red_expr S C (spec_object_can_put_6 Ad bext) o ->
      red_expr S C (spec_object_can_put_5 l (attributes_data_of Ad)) o

  | red_spec_object_can_put_6_extens_false : forall S C Ad, (* Step 8.a *)
      red_expr S C (spec_object_can_put_6 Ad false) (out_ter S false)

  | red_spec_object_can_put_6_extens_true : forall S C Ad b o, (* Step 8.b *)
      b = attributes_data_writable Ad ->
      red_expr S C (spec_object_can_put_6 Ad true) (out_ter S b)

  (** Put  (8.12.5) and (8.7.2)
      Note: rules are generalized so as to also handle the Put method on primitive values *)

  | red_spec_object_put_1_default : forall S C vthis l x v throw o1 o, (* Step 1 *)
      red_expr S C (spec_object_can_put l x) o1 ->
      red_expr S C (spec_object_put_2 vthis l x v throw o1) o ->
      red_expr S C (spec_object_put_1 builtin_default_put vthis l x v throw) o  

  | red_spec_object_put_1_false : forall S C vthis l x v throw o, (* Steps 1.a and 1.b *)
      red_expr S C (spec_error_or_void throw builtin_type_error) o ->
      red_expr S C (spec_object_put_2 vthis l x v throw (out_ter S false)) o

  | red_spec_object_put_2_true : forall S C vthis l x v throw o, (* Step 2 *)
      red_expr S C (spec_object_get_own_prop l x (spec_object_put_3 vthis l x v throw)) o ->      
      red_expr S C (spec_object_put_2 vthis l x v throw (out_ter S true)) o

  | red_spec_object_put_3_data_object : forall S C (lthis:object_loc) l x v throw Ad Desc o1 o, (* Step 3 *)
      Desc = descriptor_intro (Some v) None None None None None ->
      red_expr S C (spec_object_define_own_prop l x Desc throw) o1 ->
      red_expr S C (spec_object_put_5 o1) o ->
      red_expr S C (spec_object_put_3 lthis l x v throw (attributes_data_of Ad)) o

  | red_spec_object_put_3_data_prim : forall S C (wthis:prim) l x v throw Ad o, (* Step 3, for prim values *)
      red_expr S C (spec_error_or_void throw builtin_type_error) o ->
      red_expr S C (spec_object_put_3 wthis l x v throw (attributes_data_of Ad)) o

  | red_spec_object_put_3_not_data : forall S C vthis l x v throw Aa o, (* Step 4 *)
      red_expr S C (spec_object_get_prop l x (spec_object_put_4 vthis l x v throw)) o ->
      red_expr S C (spec_object_put_3 vthis l x v throw (attributes_accessor_of Aa)) o
      (* According to the spec, it should be every cases that are not [attributes_data_of].  There thus lacks a case there:  [full_descriptor_undef]. -- Martin *)

  | red_spec_object_put_4_accessor : forall vsetter lfsetter S C vthis l x v throw Aa o1 o, (* Step 5 *)
      vsetter = attributes_accessor_set Aa ->
      vsetter <> undef -> (* Note: this premise is a derived fact *)
      vsetter = value_object lfsetter ->
      red_expr S C (spec_call lfsetter vthis (v::nil)) o1 ->
      red_expr S C (spec_object_put_5 o1) o ->
      red_expr S C (spec_object_put_4 vthis l x v throw (attributes_accessor_of Aa)) o

  | red_spec_object_put_4_not_accessor_object : forall S C (lthis:object_loc) l x v throw Ad Desc o1 o, (* Step 6 *)
      Desc = descriptor_intro_data v true true true ->
      red_expr S C (spec_object_define_own_prop l x Desc throw) o1 ->
      red_expr S C (spec_object_put_5 o1) o ->
      red_expr S C (spec_object_put_4 lthis l x v throw (attributes_data_of Ad)) o
      (* According to the spec, it should be every cases that are not [attributes_accessor_of].  There thus lacks a case there:  [full_descriptor_undef]. -- Martin *)

  | red_spec_object_put_4_not_accessor_prim : forall S C (wthis:prim) l x v throw Ad o, (* Step 6, for prim values *)
      red_expr S C (spec_error_or_void throw builtin_type_error) o ->
      red_expr S C (spec_object_put_4 wthis l x v throw (attributes_data_of Ad)) o

  | red_spec_object_put_5_return : forall S C rv, (* Steps 3.c and 7 *)
      red_expr S C (spec_object_put_5 (out_ter S rv)) (out_void S)

  (** HasProperty  (8.12.6) *)

  | red_spec_object_has_prop_1_default : forall o1 S C l x o, (* Step 1 *)
      red_expr S C (spec_object_get_prop l x spec_object_has_prop_2) o ->
      red_expr S C (spec_object_has_prop_1 builtin_default_has_prop l x) o  

  | red_spec_object_has_prop_2 : forall S C D b, (* Steps 2 and 3 *)
      b = (If D = full_descriptor_undef then false else true) ->
      red_expr S C (spec_object_has_prop_2 D) (out_ter S b)

  (** Delete  (8.12.7) *)

  | red_spec_object_delete_1_default : forall S C l x throw o, (* Step 1 *)
      red_expr S C (spec_object_get_own_prop l x (spec_object_delete_2 l x throw)) o ->
      red_expr S C (spec_object_delete_1 builtin_default_delete l x throw) o  

  | red_spec_object_delete_2_undef : forall S C l x throw, (* Step 2 *)
      red_expr S C (spec_object_delete_2 l x throw full_descriptor_undef) (out_ter S true)

  | red_spec_object_delete_2_some_configurable : forall S C l x throw A S' o, (* Step 3 *)
      attributes_configurable A = true ->
      object_rem_property S l x S' ->
      red_expr S C (spec_object_delete_2 l x throw (full_descriptor_some A)) (out_ter S' true)

  | red_spec_object_delete_3_some_non_configurable : forall S C l x throw A o, (* Steps 4 and 5 *)
      attributes_configurable A = false ->
      red_expr S C (spec_error_or_cst throw builtin_type_error false) o ->
      red_expr S C (spec_object_delete_2 l x throw (full_descriptor_some A)) o 

  (** DefaultValue  (8.12.8)
      Note: rules are better factorized than the specification *)

  | red_spec_object_default_value_1_default : forall S C l prefo pref o,
      pref = unsome_default preftype_number prefo ->
      red_expr S C (spec_object_default_value_2 l pref (other_preftypes pref)) o ->
      red_expr S C (spec_object_default_value_1 builtin_default_default_value l prefo) o  
  
  | red_spec_object_default_value_2 : forall S C l pref1 pref2 o,
      red_expr S C (spec_object_default_value_sub_1 l (method_of_preftype pref1) (spec_object_default_value_3 l pref2)) o ->
      red_expr S C (spec_object_default_value_2 l pref1 pref2) o

  | red_spec_object_default_value_3 : forall S C l pref2 o,
      red_expr S C (spec_object_default_value_sub_1 l (method_of_preftype pref2) spec_object_default_value_4) o ->
      red_expr S C (spec_object_default_value_3 l pref2) o

  | red_spec_object_default_value_4 : forall S C o,
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C spec_object_default_value_4 o

  (** Auxiliary reduction rules for DefaultValue (in continuation-passing-style) *)

  | red_spec_object_default_value_sub_1 : forall o1 S C l x K o,
      red_expr S C (spec_object_get l x) o1 ->
      red_expr S C (spec_object_default_value_sub_2 l o1 K) o ->
      red_expr S C (spec_object_default_value_sub_1 l x K) o

  | red_spec_object_default_value_sub_2_not_callable : forall S0 S C l v K o,
      callable S v None ->
      red_expr S C K o ->
      red_expr S0 C (spec_object_default_value_sub_2 l (out_ter S v) K) o

  | red_spec_object_default_value_sub_2_callable : forall S C lfunc l v K o B o1,
      callable S v (Some B) ->
      v = value_object lfunc ->
      red_expr S C (spec_call lfunc l nil) o1 ->
      red_expr S C (spec_object_default_value_sub_3 o1 K) o ->
      red_expr S C (spec_object_default_value_sub_2 l (out_ter S v) K) o
      (* Note: the spec does not mention a call [getValue] on the result of the [[call]] *)

  | red_spec_object_default_value_sub_3_prim : forall S0 S C K w,
      red_expr S0 C (spec_object_default_value_sub_3 (out_ter S w) K) (out_ter S w)

  | red_spec_object_default_value_sub_3_object : forall S0 S C l K o,
      red_expr S C K o ->
      red_expr S0 C (spec_object_default_value_sub_3 (out_ter S (value_object l)) K) o

  (** DefineOwnProperty  (8.12.9) *)

  | red_spec_object_define_own_prop_1_default : forall S C l x Desc throw o,(* Step 1 *)
      red_expr S C (spec_object_get_own_prop l x (spec_object_define_own_prop_2 l x Desc throw)) o ->
      red_expr S C (spec_object_define_own_prop_1 builtin_default_define_own_prop l x Desc throw) o 

  | red_spec_object_define_own_prop_2 : forall S C l x Desc throw An bext o, (* Step 2 *)
      object_extensible S l bext ->
      red_expr S C (spec_object_define_own_prop_3 l x Desc throw An bext) o ->
      red_expr S C (spec_object_define_own_prop_2 l x Desc throw An) o

  | red_spec_object_define_own_prop_3_undef_false : forall S C l x Desc throw o, (* Step 3 *)
      red_expr S C (spec_object_define_own_prop_reject throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x Desc throw full_descriptor_undef false) o

  | red_spec_object_define_own_prop_3_undef_true : forall S C l x Desc throw A S', (* Step 4 *)
      A = (If (descriptor_is_generic Desc \/ descriptor_is_data Desc)
            then attributes_data_of_descriptor Desc
            else attributes_accessor_of_descriptor Desc) ->
      object_set_property S l x A S' ->
      red_expr S C (spec_object_define_own_prop_3 l x Desc throw full_descriptor_undef true) (out_ter S' true)

  | red_spec_object_define_own_prop_3_includes : forall S C l x A Desc throw bext, (* Step 6 (subsumes 5) *)
      descriptor_contains A Desc ->
      red_expr S C (spec_object_define_own_prop_3 l x Desc throw (full_descriptor_some A) bext) (out_ter S true)

  | red_spec_object_define_own_prop_3_not_include : forall S C l x A Desc throw o bext, (* Steps 6 else branch *)
      ~ descriptor_contains A Desc ->
      red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_3 l x Desc throw (full_descriptor_some A) bext) o

  | red_spec_object_define_own_prop_4_reject : forall S C l x A Desc throw o, (* Step 7 *)
      attributes_change_enumerable_on_non_configurable A Desc ->
      red_expr S C (spec_object_define_own_prop_reject throw) o ->
      red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o 

  | red_spec_object_define_own_prop_4_not_reject : forall S C l x A Desc throw o, (* Step 7 else branch *)
      ~ attributes_change_enumerable_on_non_configurable A Desc ->
      red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o

  | red_spec_object_define_own_prop_5_generic : forall S C l x A Desc throw o, (* Step 8 *)
      descriptor_is_generic Desc ->
      red_expr S C (spec_object_define_own_prop_write l x A Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o

  | red_spec_object_define_own_prop_5_a : forall S C l x A Desc throw o,(* Step 9 *)
      (attributes_is_data A) <> (descriptor_is_data Desc) ->
      red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o

  | red_spec_object_define_own_prop_6a_reject : forall S C l x A Desc throw o, (* Step 9a *)
      attributes_configurable A = false ->
      red_expr S C (spec_object_define_own_prop_reject throw) o ->
      red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o

  | red_spec_object_define_own_prop_6a_accept : forall S S' C l x A A' Desc throw o, (* Steps 9b and 9c *)
      attributes_configurable A = true ->
      A' = match A with
           | attributes_data_of Ad => attributes_accessor_of_attributes_data Ad
           | attributes_accessor_of Aa => attributes_data_of_attributes_accessor Aa
           end ->
      object_set_property S l x A' S' ->
      red_expr S' C (spec_object_define_own_prop_write l x A' Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o

  | red_spec_object_define_own_prop_5_b : forall S C l x Ad Desc throw o, (* Step 10 *)
      descriptor_is_data Desc ->
      red_expr S C (spec_object_define_own_prop_6b l x Ad Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_5 l x (attributes_data_of Ad) Desc throw) o

  | red_spec_object_define_own_prop_6b_false_reject : forall S C l x Ad Desc throw o, (* Step 10a *)
      attributes_change_data_on_non_configurable Ad Desc ->
      red_expr S C (spec_object_define_own_prop_reject throw) o ->
      red_expr S C (spec_object_define_own_prop_6b l x Ad Desc throw) o

  | red_spec_object_define_own_prop_6b_false_accept : forall S C l x Ad Desc throw o, (* Step 10a else branch *)
      ~ (attributes_change_data_on_non_configurable Ad Desc) ->
      red_expr S C (spec_object_define_own_prop_write l x Ad Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_6b l x Ad Desc throw) o

  | red_spec_object_define_own_prop_5_c : forall S C l x Aa Desc throw o, (* Step 11 *)
      descriptor_is_accessor Desc ->
      red_expr S C (spec_object_define_own_prop_6c l x Aa Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_5 l x (attributes_accessor_of Aa) Desc throw) o

  | red_spec_object_define_own_prop_6c_1 : forall S C l x Aa Desc throw o, (* Step 11a *)
      attributes_change_accessor_on_non_configurable Aa Desc ->
      red_expr S C (spec_object_define_own_prop_reject throw) o ->
      red_expr S C (spec_object_define_own_prop_6c l x Aa Desc throw) o

   | red_spec_object_define_own_prop_6c_2 : forall S C l x Aa Desc throw o, (* Step 11a else branch *)
      ~ attributes_change_accessor_on_non_configurable Aa Desc ->
      red_expr S C (spec_object_define_own_prop_write l x Aa Desc throw) o ->
      red_expr S C (spec_object_define_own_prop_6c l x Aa Desc throw) o

  | red_spec_object_define_own_prop_write : forall S S' C l x A Desc throw A', 
      A' = attributes_update A Desc ->
      object_set_property S l x A' S' ->
      red_expr S C (spec_object_define_own_prop_write l x A Desc throw) (out_ter S' true)

  | red_spec_object_define_own_prop_reject : forall S C throw o, 
      red_expr S C (spec_error_or_cst throw builtin_type_error false) o ->
      red_expr S C (spec_object_define_own_prop_reject throw) o


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
        then spec_prim_value_get
        else spec_object_get) ->
      red_expr S C (ext_get v (ref_name r)) o ->
      red_expr S C (spec_get_value r) o

  | red_spec_ref_get_value_ref_c : forall L S C r o, (* Step 5. *)
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_get_binding_value L (ref_name r) (ref_strict r)) o ->
      red_expr S C (spec_get_value r) o

  (** Special Get method for primitive values (returns value)  (8.7.1) 
      Note: implemented with the same rules as [spec_object_get] *)

  | red_spec_prim_value_get : forall S C v x o1 o,
      red_expr S C (spec_to_object v) o1 ->
      red_expr S C (spec_prim_value_get_1 v x o1) o ->
      red_expr S C (spec_prim_value_get v x) o

  | red_spec_prim_value_get_1 : forall S0 S C v x l o,
      red_expr S C (spec_object_get_1 builtin_default_get v l x) o ->
      red_expr S0 C (spec_prim_value_get_1 v x (out_ter S l)) o

  (** Put value on a reference (returns void) *)

  | red_spec_ref_put_value_value : forall S C v vnew o, (* Step 1 *)
      red_expr S C (spec_error builtin_ref_error) o ->
      red_expr S C (spec_put_value v vnew) o 
    
  | red_spec_ref_put_value_ref_a_1 : forall S C r vnew o, (* Steps 2 and 3a *)
      ref_is_unresolvable r ->
      ref_strict r = true ->
      red_expr S C (spec_error builtin_ref_error) o ->
      red_expr S C (spec_put_value r vnew) o

  | red_spec_ref_put_value_ref_a_2 : forall o S C r vnew, (* Steps 2 and 3b *)
      ref_is_unresolvable r ->
      ref_strict r = false ->
      red_expr S C (spec_object_put builtin_global (ref_name r) vnew throw_false) o ->
      red_expr S C (spec_put_value r vnew) o 

  | red_spec_ref_put_value_ref_b : forall v ext_put S C r vnew o, (* Step 4 *)
      ref_is_property r ->
      ref_base r = ref_base_type_value v ->
      ext_put = (If ref_has_primitive_base r
        then spec_prim_value_put
        else spec_object_put) ->
      red_expr S C (ext_put v (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (resvalue_ref r) vnew) o
      
  | red_spec_ref_put_value_ref_c : forall L S C r vnew o, (* Step 5 *)     
      ref_base r = ref_base_type_env_loc L ->
      red_expr S C (spec_env_record_set_mutable_binding L (ref_name r) vnew (ref_strict r)) o ->
      red_expr S C (spec_put_value (resvalue_ref r) vnew) o  

  (** Special Put method for primitive values (returns value)  (8.7.2) 
      Note: implemented with the same rules as [spec_object_put]*)

  | red_spec_prim_value_put : forall S C w x v throw o1 o,
      red_expr S C (spec_to_object w) o1 ->
      red_expr S C (spec_prim_value_put_1 w x v throw o1) o ->
      red_expr S C (spec_prim_value_put w x v throw) o

  | red_spec_prim_value_put_1 : forall S0 S C w x v throw l o,
      red_expr S C (spec_object_put_1 builtin_default_put w l x v throw) o ->
      red_expr S0 C (spec_prim_value_put_1 w x v throw (out_ter S l)) o

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

  | red_spec_env_record_has_binding_1_decl : forall S C L x Ed b,
      b = (If decl_env_record_indom Ed x then true else false) ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_decl Ed)) (out_ter S b)

  | red_spec_env_record_has_binding_1_object : forall S C L x l pt o,
      red_expr S C (spec_object_has_prop l x) o ->
      red_expr S C (spec_env_record_has_binding_1 L x (env_record_object l pt)) o

  (** Create mutable binding (returns void) *)

  | red_spec_env_record_create_mutable_binding : forall S C L x deletable_opt deletable o E,
      deletable = unsome_default false deletable_opt ->
      env_record_binds S L E ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable E) o ->
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o

  | red_spec_env_record_create_mutable_binding_1_decl_indom : forall S C L x deletable Ed S',
      ~ decl_env_record_indom Ed x ->
      S' = env_record_write_decl_env S L x (mutability_of_bool deletable) undef ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_decl Ed)) (out_void S')

  | red_spec_env_record_create_mutable_binding_1_object : forall o1 S C L x deletable l pt o,
      red_expr S C (spec_object_has_prop l x) o1 ->
      red_expr S C (spec_env_record_create_mutable_binding_2 L x deletable l o1) o ->
      red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_object l pt)) o

  | red_spec_env_record_create_mutable_binding_obj_2 : forall A S0 C L x deletable l S o1 o,
      A = attributes_data_intro undef true true deletable ->
      red_expr S C (spec_object_define_own_prop l x A throw_true) o1 ->
      red_expr S C (spec_env_record_create_mutable_binding_3 o1) o ->
      red_expr S0 C (spec_env_record_create_mutable_binding_2 L x deletable l (out_ter S false)) o

  | red_spec_env_record_create_mutable_binding_obj_3 : forall S0 S C rv,
      red_expr S0 C (spec_env_record_create_mutable_binding_3 (out_ter S rv)) (out_void S)

  (** Set mutable binding (returns void) *)

  | red_spec_env_record_set_mutable_binding : forall S C L x v str o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str E) o ->
      red_expr S C (spec_env_record_set_mutable_binding L x v str) o

  | red_spec_env_record_set_mutable_binding_1_decl : forall v_old mu S C L x v str Ed K o,
      decl_env_record_binds Ed x mu v_old ->
      K = (If mutability_is_mutable mu
            then (let S' := env_record_write_decl_env S L x mu v in
                  spec_returns (out_void S'))
            else (spec_error_or_void str builtin_type_error)) ->
      red_expr S C K o ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str (env_record_decl Ed)) o

  | red_spec_env_record_set_mutable_binding_1_object : forall S C L x v str l pt o,
      red_expr S C (spec_object_put l x v str) o ->
      red_expr S C (spec_env_record_set_mutable_binding_1 L x v str (env_record_object l pt)) o

  (** Get binding value (returns value) *)

  | red_spec_env_record_get_binding_value : forall E S C L x str o,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_get_binding_value_1 L x str E) o ->
      red_expr S C (spec_env_record_get_binding_value L x str) o

  | red_spec_env_record_get_binding_value_1_decl : forall mu v S C L x str Ed K o,
      decl_env_record_binds Ed x mu v -> 
      K = (If mu = mutability_uninitialized_immutable
              then (spec_error_or_cst str builtin_ref_error undef)
              else spec_returns (out_ter S v)) ->
      red_expr S C K o ->
      red_expr S C (spec_env_record_get_binding_value_1 L x str (env_record_decl Ed)) o

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

  | red_spec_env_record_delete_binding_1_decl_indom : forall mu v S C L x Ed S' b,
      decl_env_record_binds Ed x mu v ->
      (If mu = mutability_deletable
          then (S' = env_record_write S L (decl_env_record_rem Ed x) /\ b = true)
          else (S' = S /\ b = false)) ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl Ed)) (out_ter S' b)

  | red_spec_env_record_delete_binding_1_decl_not_indom : forall S C L x Ed,
      ~ decl_env_record_indom Ed x ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl Ed)) (out_ter S true)

  | red_spec_env_record_delete_binding_1_object : forall S C L x l pt o,
      red_expr S C (spec_object_delete l x throw_false) o ->
      red_expr S C (spec_env_record_delete_binding_1 L x (env_record_object l pt)) o

  (** Implicit this value (returns value) *)

  | red_spec_env_record_implicit_this_value : forall S C L o E,
      env_record_binds S L E ->
      red_expr S C (spec_env_record_implicit_this_value_1 L E) o ->
      red_expr S C (spec_env_record_implicit_this_value L) o

  | red_spec_env_record_implicit_this_value_1_decl : forall S C L Ed,
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_decl Ed)) (out_ter S undef)

  | red_spec_env_record_implicit_this_value_1_object : forall S C L l (pt : bool) v,
      v = (if pt then l else undef) ->
      red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_object l pt)) (out_ter S v)

  (** Create immutable binding (returns void) *)

  | red_spec_env_record_create_immutable_binding : forall Ed S C L x S',
      env_record_binds S L (env_record_decl Ed) ->
      ~ decl_env_record_indom Ed x ->
      S' = env_record_write_decl_env S L x mutability_uninitialized_immutable undef ->
      red_expr S C (spec_env_record_create_immutable_binding L x) (out_void S')

  (** Initialize immutable binding (returns void) *)

  | red_spec_env_record_initialize_immutable_binding : forall Ed v_old S C L x v S',
      env_record_binds S L (env_record_decl Ed) ->
      decl_env_record_binds Ed x mutability_uninitialized_immutable v_old -> (* Note: v_old is always undef here *)
      S' = env_record_write_decl_env S L x mutability_immutable v ->
      red_expr S C (spec_env_record_initialize_immutable_binding L x v) (out_void S')

  (** Auxiliary: combination of create mutable binding and set mutable binding (returns void) *)

  | red_spec_env_record_create_set_mutable_binding : forall S C L x deletable_opt v str o o1,
      red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o1 ->
      red_expr S C (spec_env_record_create_set_mutable_binding_1 o1 L x v str) o ->
      red_expr S C (spec_env_record_create_set_mutable_binding L x deletable_opt v str) o

  | red_spec_env_record_create_set_mutable_binding_1 : forall S S0 C L x v str o,
      red_expr S C (spec_env_record_set_mutable_binding L x v str) o ->
      red_expr S0 C (spec_env_record_create_set_mutable_binding_1 (out_void S) L x v str) o


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
      
  | red_spec_entering_eval_code : forall S C bd o,
      (* TODO! *)
      red_expr S C (spec_entering_eval_code bd) o  

  (** Entering function code  (10.4.3) *)

  (* TODO: make this CPS *)
  | red_spec_entering_func_code : forall S C lf vthis args bd str o, 
      object_code S lf (Some bd) ->
      str = funcbody_is_strict bd ->
      red_expr S C (spec_entering_func_code_1 lf args bd vthis str) o ->
      red_expr S C (spec_entering_func_code lf vthis args) o

  | red_spec_entering_func_code_1_strict : forall S C lf args bd vthis o, (* Step 1 *)
      red_expr S C (spec_entering_func_code_3 lf args true bd vthis) o -> 
      red_expr S C (spec_entering_func_code_1 lf args bd vthis true) o

  | red_spec_entering_func_code_1_null_or_undef : forall S C lf args str bd vthis o, (* Step 2 *)
      (vthis = null \/ vthis = undef) ->
      red_expr S C (spec_entering_func_code_3 lf args false bd builtin_global) o ->
      red_expr S C (spec_entering_func_code_1 lf args bd vthis false) o

  | red_spec_entering_func_code_1_not_object : forall S C lf args bd vthis o1 o, (* Step 3 *)
      (vthis <> null /\ vthis <> undef /\ type_of vthis <> type_object) ->
      red_expr S C (spec_to_object vthis) o1 ->
      red_expr S C (spec_entering_func_code_2 lf args bd o1) o ->
      red_expr S C (spec_entering_func_code_1 lf args bd vthis false) o

  | red_spec_entering_func_code_2 : forall S S0 C lf args bd vthis o,
      red_expr S C (spec_entering_func_code_3 lf args false bd vthis) o ->
      red_expr S0 C (spec_entering_func_code_2 lf args bd (out_ter S vthis)) o

  | red_spec_entering_func_code_1_object : forall S C lf args bd (lthis:object_loc) o, (* Step 4 *)
      red_expr S C (spec_entering_func_code_3 lf args false bd lthis) o ->
      red_expr S C (spec_entering_func_code_1 lf args bd lthis false) o

  | red_spec_entering_func_code_3 : forall S C lf args str bd vthis lex lex' S' C' o, (* Steps 5 through 9 *)
      object_scope S lf (Some lex) ->
      (lex', S') = lexical_env_alloc_decl S lex ->
      C' = execution_ctx_intro_same lex' vthis str ->
      red_expr S' C' (spec_execution_ctx_binding_instantiation codetype_func (Some lf) (funcbody_prog bd) args) o -> (* rename o to o1 *)
      (* TODO: add new premise: red S C' (spec_entering_func_code_4 K o1) *)
      red_expr S C (spec_entering_func_code_3 lf args str bd vthis) o 

      (*  TODO:   
          red S C' K o ->
          red S0 C' (spec_entering_func_code_4 K (out_void S)) o 
          
          interpreter schema:
             red_entering_func_code S C f :=
                let C' = ... in
                if_void (red_binding_inst S C' f) (fun S' =>
                   red_call S' C' f.body)  // K=red_call
          *)

  (*------------------------------------------------------------*)
  (** Binding instantiation (10.5) *)   

  (* Auxiliary reductions for binding instantiation:
     bindings for parameters (Step 4d). *)

  (* TODO: don't need to do this in CPS *)

  | red_spec_binding_instantiation_formal_params_empty : forall S C K args L o,  (* Loop ends in Step 4d *)  
      red_expr S C (K args L) o -> (* todo: simply return out_void here *)
      red_expr S C (spec_binding_instantiation_formal_params K args L nil) o

  | red_spec_binding_instantiation_formal_params_non_empty : forall o1 S C K v args args' L x xs o, (* Steps 4d i - iii *)
      (v,args') = (match args with nil => (undef,nil) | v::args' => (v,args') end) ->
      red_expr S C (spec_env_record_has_binding L x) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_1 K args' L x xs v o1) o ->
      red_expr S C (spec_binding_instantiation_formal_params K args L (x::xs)) o

  | red_spec_binding_instantiation_formal_params_1_declared : forall o1 S0 S C K args L x xs v o,  (* Step 4d iv *)
      red_expr S C (spec_env_record_set_mutable_binding L x v (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L xs o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L x xs v (out_ter S true)) o

  | red_spec_binding_instantiation_formal_params_1_not_declared : forall S0 S C K args L x xs v o o1, (* Step 4d iv *)
    (* TODO: replace (execution_ctx_strict C) with  (prog_strict code) *)
      red_expr S C (spec_env_record_create_set_mutable_binding L x None v (execution_ctx_strict C)) o1 ->
      (* TODO(Daiva): are we sure that deletable_opt above is None, meaning that the item
         will not be deletable? it's worth testing in an implementation if you can delete an arg binding. *)
      red_expr S C (spec_binding_instantiation_formal_params_2 K args L xs o1) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_1 K args L x xs v (out_ter S false)) o

    (* TODO: change above to do :
            -- if has binding -> create and goto join 
            -- if no binding -> goto join
            -- on join: to set
      *)

  | red_spec_binding_instantiation_formal_params_2 : forall S0 S C K args L xs o1 o, (* Step 4d loop *)
      red_expr S C (spec_binding_instantiation_formal_params K args L xs) o ->
      red_expr S0 C (spec_binding_instantiation_formal_params_2 K args L xs (out_void S)) o

  (* Auxiliary reductions for binding instantiation: 
     bindings for function declarations (Step 5). *)
  
  (* TODO(Daiva): an entry point such as 
     [spec_binding_instantiation_function_decls] should not include an [o] as last argument.
     These [o] should be eliminated before, before making the transition to this form. *)

(* --start arthur still needs to read-- *)
  | red_spec_binding_instantiation_function_decls_nil : forall o1 L S0 S C K args bconfig o, (* Step 5b *)
      red_expr S C (K L) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L nil bconfig (out_void S)) o

  | red_spec_binding_instantiation_function_decls_cons : forall o1 L S0 S C K args fd fds bconfig o, (* Step 5b *)
      let str := funcbody_is_strict (funcdecl_body fd) in
      red_expr S C (spec_creating_function_object (funcdecl_parameters fd) (funcdecl_body fd) (execution_ctx_variable_env C) str) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_1 K args L fd fds str bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls K args L (fd::fds) bconfig (out_void S)) o

  | red_spec_binding_instantiation_function_decls_1 : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5c *)
      red_expr S C (spec_env_record_has_binding L (funcdecl_name fd)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_1 K args L fd fds str bconfig (out_ter S fo)) o

  | red_spec_binding_instantiation_function_decls_2_false : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5d *)
      red_expr S C (spec_env_record_create_mutable_binding L (funcdecl_name fd) (Some bconfig)) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig (out_ter S false)) o

  | red_spec_binding_instantiation_function_decls_2_true_global : forall K1 A o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5e ii *)
        (* todo: remove A *)
      K1 = spec_binding_instantiation_function_decls_3 K args fd fds str fo (attributes_configurable A) bconfig -> (* What is this [A]?  I guess this should be tested after [spec_object_get_prop] have been executed, otherwise it's meaningless. -- Martin *)
      red_expr S C (spec_object_get_prop builtin_global (funcdecl_name fd) K1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args env_loc_global_env_record fd fds str fo bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_function_decls_3_true : forall o1 L S C K args fd fds str fo bconfig o, (* Step 5e iii *)
       let A := attributes_data_intro undef true true bconfig in (* todo: something wrong with A , attempted fix below *)
      (* attributes_configurable A = true -> *)
      red_expr S C (spec_object_define_own_prop builtin_global (funcdecl_name fd) A true) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds str fo bconfig o1) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo true bconfig A) o

  | red_spec_binding_instantiation_function_decls_3_false_type_error : forall o1 L S C K args fd fds str fo A configurable bconfig o, (* Step 5e iv *)
      (* attributes_configurable A = false -> *)
      configurable <> true ->
      descriptor_is_accessor A \/ (attributes_writable A = false \/ attributes_enumerable A = false) ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo configurable bconfig A) (out_type_error S)

(* todo : pattern match A in the goal with (attributes_data_of Ad) 
   and then check  ~ (attributes_data_writable Ad = true /\ attributes_data_enumerable Ad = true) *)

  | red_spec_binding_instantiation_function_decls_3_false : forall o1 L S C K args fd fds str fo A configurable bconfig o, (* Step 5e iv *)
     configurable <> true ->
      ~ (descriptor_is_accessor A) /\ attributes_writable A = true /\ attributes_enumerable A = true ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args env_loc_global_env_record fd fds str fo bconfig (out_void S)) o ->
      red_expr S C (spec_binding_instantiation_function_decls_3 K args fd fds str fo configurable bconfig A) o

  | red_spec_binding_instantiation_function_decls_2_true : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5e *)
      L <> env_loc_global_env_record ->
      red_expr S C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_2 K args L fd fds str fo bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_function_decls_4 : forall o1 L S0 S C K args fd fds str fo bconfig o, (* Step 5f *)
      red_expr S C (spec_env_record_set_mutable_binding L (funcdecl_name fd) (value_object fo) str) o1 ->
      red_expr S C (spec_binding_instantiation_function_decls K args L fds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_function_decls_4 K args L fd fds str fo bconfig (out_void S)) o
      
  (* Auxiliary reductions for binding instantiation:
     bindings for variable declarations (Step 8) *)

  (* _nil _cons as naming for the reduction rules *)
  | red_spec_binding_instantiation_var_decls_empty : forall o1 L S0 S C bconfig o, (* Step 8 *)
      red_expr S0 C (spec_binding_instantiation_var_decls L nil bconfig (out_void S)) (out_void S)     
      
  | red_spec_binding_instantiation_var_decls_non_empty : forall o1 L S0 S C vd vds bconfig o, (* Step 8b *)
      red_expr S C (spec_env_record_has_binding L vd) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls_1 L vd vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls L (vd::vds) bconfig (out_void S)) o
      (* TODO: remove (out_void S) from spec_binding_instantiation_var_decls *)

  | red_spec_binding_inst_var_decls_1_true : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S true)) o

  | red_spec_binding_instantiation_var_decls_1_false : forall o1 L S0 S C vd vds bconfig o, (* Step 8c *)
      (* todo: replace (execution_ctx_strict C) with the right thing *)
      red_expr S C (spec_env_record_create_set_mutable_binding L vd (Some bconfig) undef (execution_ctx_strict C)) o1 ->
      red_expr S C (spec_binding_instantiation_var_decls L vds bconfig o1) o ->
      red_expr S0 C (spec_binding_instantiation_var_decls_1 L vd vds bconfig (out_ter S false)) o

(* --end arthur still needs to read-- *)      

  (* Auxiliary reductions for binding instantiation:
     Declaring Arguments Object (7) *)
      
        (* TODO: simplify because now we are only called when bdecl=false *)
  | red_spec_binding_instantiation_arg_obj_declared : forall o1 L S0 S C K ct lf code xs args bdecl o, (* Step 7 else branch *)
      ~ (ct = codetype_func /\ bdecl = false) ->
      red_expr S C (K (out_void S)) o ->
      red_expr S0 C (spec_binding_instantiation_arg_obj K ct lf code xs args L (out_ter S bdecl)) o (* I removed the constraint that [lf] should be defined.  Please double check -- Martin.*)

  | red_spec_binding_instantiation_arg_obj_not_declared : forall str o1 L S0 S C K ct lf code xs args o, (* Step 7a *)
      str = prog_strict code ->
      red_expr S C (spec_create_arguments_object lf xs args L str) o1 ->
      red_expr S C (spec_binding_instantiation_arg_obj_1 K code L str o1) o ->
      red_expr S0 C (spec_binding_instantiation_arg_obj K codetype_func (Some lf) code xs args L (out_ter S false)) o
 
  | red_spec_binding_instantiation_arg_obj_1_strict : forall o1 L S0 S C K ct code largs o, (* Step 7b i *)
      red_expr S C (spec_env_record_create_immutable_binding L "arguments") o1 -> 
      red_expr S C (spec_binding_instantiation_arg_obj_2 K code L largs o1) o ->
      red_expr S0 C (spec_binding_instantiation_arg_obj_1 K code L true (out_ter S largs)) o

  | red_spec_binding_instantiation_arg_obj_2 : forall o1 L S0 S C K code largs o, (* Step 7b ii *)
      red_expr S C (spec_env_record_initialize_immutable_binding L "arguments" (value_object largs)) o1 -> 
      red_expr S C (K o1) o ->
      red_expr S0 C (spec_binding_instantiation_arg_obj_2 K code L largs (out_void S)) o
      
  | red_spec_binding_instantiation_arg_obj_1_not_strict : forall o1 L S0 S C K ct code largs o, (* Step 7c *)
      red_expr S C (spec_env_record_create_set_mutable_binding L "arguments" None largs false) o1 -> 
      red_expr S C (K o1) o ->
      red_expr S0 C (spec_binding_instantiation_arg_obj_1 K code L false (out_ter S largs)) o

  (* Declaration Binding Instantiation: main reduction rules *)    

  | red_spec_execution_ctx_binding_instantiation : forall L Ls S C ct lf code args o, (* Step 1 *)
      (* todo: Daiva -- I think that strictness is not handled correctly at the moment. We need to implement 10.1.1 *)
      (* todo: [code] needs to contain all the function declarations and the variable declarations *)
      execution_ctx_variable_env C = L::Ls ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 ct lf code args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation ct lf code args) o

  | red_spec_execution_ctx_binding_instantiation_1_function : forall xs S C lf code args L o, (* Step 4a *)
      object_formal_parameters S lf (Some xs) ->
      red_expr S C (spec_binding_instantiation_formal_params (spec_execution_ctx_binding_instantiation_2 codetype_func (Some lf) code xs) args L xs) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 codetype_func (Some lf) code args L) o

  | red_spec_execution_ctx_binding_instantiation_1_not_function : forall L S C ct code args o, (* Skipping step 4a *)
      ct <> codetype_func ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 ct None code nil args L) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_1 ct None code args L) o

  | red_spec_execution_ctx_binding_instantiation_function_2 : forall bconfig L K S C ct lf code fds xs args o, (* Step 5 *)
      bconfig = (If ct = codetype_eval then true else false) ->
      fds = prog_funcdecl code -> 
      (* TODO: remove continuation if possible for spec_binding_instantiation_function_decls *)
      K = spec_execution_ctx_binding_instantiation_3 ct lf code xs args bconfig -> 
      red_expr S C (spec_binding_instantiation_function_decls K args L fds bconfig (out_void S)) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_2 ct lf code xs args L) o
      
  | red_spec_execution_ctx_binding_instantiation_3 : forall o1 L S C K ct lf code xs args bconfig o, (* Step 6 *)
      red_expr S C (spec_env_record_has_binding L "arguments") o1 ->
      K = spec_execution_ctx_binding_instantiation_4 code bconfig L ->
      red_expr S C (spec_binding_instantiation_arg_obj K ct lf code xs args L o1) o ->
      red_expr S C (spec_execution_ctx_binding_instantiation_3 ct lf code xs args bconfig L) o

  (* TODO
      red_expr S C (spec_env_record_has_binding L "arguments") o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_4 ct lf code xs args bconfig L o1) o
      red_expr S C (spec_execution_ctx_binding_instantiation_3 ct lf code xs args bconfig L) o

      spec_execution_ctx_binding_instantiation_5 ct lf code xs args bconfig L o1 ->
      red_expr S C (spec_execution_ctx_binding_instantiation_5 ct lf code xs args bconfig L o1) o
      red_expr S C (spec_execution_ctx_binding_instantiation_4 ct lf code xs args bconfig L (false)) o

      red_expr S C (spec_execution_ctx_binding_instantiation_5 ct lf code xs args bconfig L (true)) o
      red_expr S C (spec_execution_ctx_binding_instantiation_4 ct lf code xs args bconfig L (true)) o
  *)

  | red_spec_execution_ctx_binding_instantiation_4 : forall o1 S0 L S C code bconfig o, (* Step 8 *)
      red_expr S C (spec_binding_instantiation_var_decls L (prog_vardecl code) bconfig (out_void S)) o ->
      red_expr S0 C (spec_execution_ctx_binding_instantiation_4 code bconfig L (out_void S)) o


  (*------------------------------------------------------------*)
  (** TODO: 10.6 Arguments Object (returns location to an arguments object) *)  
  (* spec_create_arguments_object *)   

  (*------------------------------------------------------------*)
  (** Function calls *)   

(*---start todo---*)


  (** Creating function object *)
    
  | red_spec_creating_function_object_proto : forall o1 S0 S C K l b o, 
      red_expr S C (spec_constructor_builtin builtin_object_new nil) o1 ->
      red_expr S C (spec_creating_function_object_proto_1 K l o1) o ->
      red_expr S0 C (spec_creating_function_object_proto K l (out_ter S b)) o
    
  | red_spec_creating_function_object_proto_1 : forall o1 S0 S C K l lproto b o, 
      let A := attributes_data_intro (value_object l) true false true in 
      red_expr S C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
      red_expr S C (spec_creating_function_object_proto_2 K l lproto o1) o ->
      red_expr S0 C (spec_creating_function_object_proto_1 K l (out_ter S lproto)) o
      
   | red_spec_creating_function_object_proto_2 : forall o1 S0 S C K l lproto b o, 
      let A := attributes_data_intro (value_object lproto) true false false in 
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
      let A := attributes_data_intro (JsNumber.of_int (length names)) false false false in 
      red_expr S' C (spec_object_define_own_prop l "length" A false) o1 ->
      red_expr S' C (spec_creating_function_object_proto (spec_creating_function_object_1 str l) l o1) o ->
      red_expr S C (spec_creating_function_object names bd X str) o
                     


   | red_spec_creating_function_object_1_not_strict : forall o1 S0 S C l b, 
      red_expr S0 C (spec_creating_function_object_1 false l (out_ter S b)) (out_ter S l)
      
   | red_spec_creating_function_object_1_strict : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := attributes_accessor_intro vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "caller" A false) o1 ->
      red_expr S C (spec_creating_function_object_2 l o1) o ->
      red_expr S0 C (spec_creating_function_object_1 true l (out_ter S b)) o
      
  | red_spec_creating_function_object_2 : forall o1 S0 S C l b o, 
      let vthrower := value_object builtin_function_throw_type_error in
      let A := attributes_accessor_intro vthrower vthrower false false in 
      red_expr S C (spec_object_define_own_prop l "arguments" A false) o1 ->
      red_expr S C (spec_creating_function_object_3 l o1) o ->
      red_expr S0 C (spec_creating_function_object_2 l (out_ter S b)) o
      
  | red_spec_creating_function_object_3 : forall o1 S0 S C l b o, 
      red_expr S0 C (spec_creating_function_object_3 l (out_ter S b)) (out_ter S l)
      
  | red_spec_call : forall builtin S C l this args o,
      object_call S l (Some builtin) ->
      red_expr S C (spec_call_1 builtin l this args) o ->
      red_expr S C (spec_call l this args) o
      
  | red_spec_call_builtin: forall S C builtinid lo this args o,
      builtinid <> builtin_spec_op_function_call /\ builtinid <> builtin_spec_op_function_bind_call ->
      red_expr S C (spec_call_builtin builtinid args) o -> 
      red_expr S C (spec_call_1 builtinid lo this args) o
      
  | red_spec_call_p: forall S C l this args o,
      red_expr S C (spec_op_function_call l this args) o -> 
      red_expr S C (spec_call_1 builtin_spec_op_function_call l this args) o
      
  | red_spec_call_prog: forall S C l this args o1 o,      
      red_expr S C (spec_entering_func_code l this args) o1 ->
      red_expr S C (spec_op_function_call_1 l o1) o ->
      (* TODO: needs to be CPS to change the context *)
      red_expr S C (spec_op_function_call l this args) o
      
  | red_spec_call_prog_1_empty: forall S0 S C l,
      (* TODO: check if red_prog return (normal, undef, empty) if function body is empty *)
      object_code S l None ->
      red_expr S0 C (spec_op_function_call_1 l (out_void S)) (out_ter S (res_normal undef))
      
  | red_spec_call_prog_1_prog: forall S0 S C l bd o1 o,
      object_code S l (Some bd) ->
      red_prog S C (funcbody_prog bd) o1 ->
      red_expr S C (spec_op_function_call_2 o1) o ->
      red_expr S0 C (spec_op_function_call_1 l (out_void S)) o
      
   (* TODO: this needs to be fixed cause it's overlapping with the abort rules...(maybe) *)
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
      
  | red_spec_function_constructor_1 : forall l' vproto O S' o1 S0 S C l args v o,
      vproto = (If (type_of v) = type_object then v else builtin_object_proto) ->
      O = object_new vproto "Object" ->
      (l', S') = object_alloc S O ->
      red_expr S' C (spec_call l (value_object l') args) o1 ->
      red_expr S' C (spec_function_constructor_2 l' o1) o ->
      red_expr S0 C (spec_function_constructor_1 l args (out_ter S v)) o
      
  | red_spec_function_constructor_2 : forall S0 S C l' v vr o,
      vr = (If (type_of v = type_object) then v else l') ->
      red_expr S0 C (spec_function_constructor_2 l' (out_ter S v)) (out_ter S vr)
      
(*            
      let A := attributes_data_intro (JsNumber.of_int (length names)) false false false in 
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
      red_expr S C (spec_call_builtin builtin_global_eval_call args) o

  | red_spec_call_global_eval_1_not_string : forall S C v,
      type_of v <> type_string ->
      red_expr S C (spec_call_global_eval_1 v) (out_ter S v)  
      
  | red_spec_call_global_eval_1_string_not_parse : forall s S C o,
      parse s None ->
      red_expr S C (spec_error builtin_syntax_error) o -> 
      red_expr S C (spec_call_global_eval_1 s) o 
      
  | red_spec_call_global_eval_1_string_parse : forall s p S C o,
      parse s (Some p) ->
      (* TODO: the entering is no longer in cps form
      red_expr S C (spec_entering_eval_code (spec_call_global_eval_1_2 p) (funcbody_intro p s)) o -> 
      *)
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
      red_expr S C (spec_call_builtin builtin_global_is_nan_call args) o

  | red_spec_call_global_is_nan_1 : forall S S0 C b n,
      b = (If n = JsNumber.nan then true else false) ->
      red_expr S0 C (spec_call_global_is_nan_1 (out_ter S n)) (out_ter S b)

  (** IsFinite (returns bool) *)

  | red_spec_call_global_is_finite : forall S C v o o1 args, 
      arguments_from args (v::nil)  ->
      red_expr S C (spec_to_number v) o1 ->
      red_expr S C (spec_call_global_is_finite_1 o1) o ->
      red_expr S C (spec_call_builtin builtin_global_is_finite_call args) o

  | red_spec_call_global_is_finite_1 : forall S S0 C b n,
      b = (If (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity) then false else true) ->
      red_expr S0 C (spec_call_global_is_finite_1 (out_ter S n)) (out_ter S b)   
    

(*------------------------------------------------------------*)
(** ** Object builtin functions (15.2) *)

  (** Object([value]) (returns object_loc)  (15.2.1.1)  *)

  | red_spec_call_object_call : forall S C args v o,
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_call_1 v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_call args) o

  | red_spec_call_object_call_1_null_or_undef : forall S C v o,
      (v = null \/ v = undef) ->
      red_expr S C (spec_call_object_new_1 v) o ->
      red_expr S C (spec_call_object_call_1 v) o

  | red_spec_call_object_call_1_other : forall S C v o,
      v <> null /\ v <> undef ->
      red_expr S C (spec_to_object v) o ->
      red_expr S C (spec_call_object_call_1 v) o

  (** new Object([value]) (returns object_loc)  (15.2.2.1) *)
  
  | red_spec_call_object_new : forall S C args v o,
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
  (* TODO: rename get_prototype into get_proto *)

  | red_spec_call_object_get_proto_of : forall S C v r args o, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_get_prototype_of_1 v) o ->
      red_expr S C (spec_constructor_builtin builtin_object_get_prototype_of_call args) o (* Isn't that a [spec_call_builtin] instead of [spec_constructor_builtin]? -- Martin *)

  | red_spec_call_object_get_proto_of_1_not_object : forall S C w o, 
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_object_get_prototype_of_1 w) o
          
  | red_spec_call_object_get_proto_of_1_object : forall S C l v, 
      object_proto S l v ->
      red_expr S C (spec_call_object_get_prototype_of_1 l) (out_ter S v)

  (** IsSealed (returns bool)  (15.2.3.11) *)  
  (* Daniele: remove comment once [red_spec_object_iter_own_prop] is fixed
  | red_spec_call_object_is_sealed : forall S C v o args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_is_sealed_1 v) o ->
      red_expr S C (spec_call_builtin builtin_object_is_sealed args) o

  | red_spec_call_object_is_sealed_1_not_object : forall S C v o, 
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_object_is_sealed_1 v) o

  (* Note: the spec says: 
        For each named own property name P of O,
          a. Let desc be the result of calling the [[GetOwnProperty]] 
             internal method of O with P.
          b. If desc.[[Configurable]] is true, then return false.
     However, in this rule we don't actually call [[GetOwnProperty]], but instead
     we directly iterate through the list of properties [(x,A)]. (since out goal 
     is just to check the [configurable] field of A, this should be safe. *)

  | red_spec_call_object_is_sealed_1_object : forall S C l x o, 
      red_expr S C (spec_object_iter_own_prop l spec_call_object_is_sealed_2 (spec_call_object_is_sealed_3 l)) -> o
      red_expr S C (spec_call_object_is_sealed_1 l) o

  | red_spec_call_object_is_sealed_2_prop_is_configurable : forall S C A K, 
      attributes_configurable A = true ->
      red_expr S C (spec_call_object_is_sealed_2 x A K) (out_ter S false)

  | red_spec_call_object_is_sealed_2_prop_is_not_configurable : forall S C A K, 
      attributes_configurable A = false ->
      red_expr S C K o ->
      red_expr S C (spec_call_object_is_sealed_2 x A K) o

 | red_spec_call_object_is_sealed_3 : forall S C l b,  
      object_extensible S l b -> 
      red_expr S C (spec_call_object_is_sealed_3 l) (out_ter S (negb b))

  (* red_spec_object_iter_own_prop *)

  | red_spec_object_iter_own_prop : forall S C P l o, 
      object_properties S l P -> 
      map_as_list P L -> 
      red_expr S C (spec_iter_properties_1 L Kprop Knil) o ->
      red_expr S C (spec_object_iter_own_prop l Kprop Knil) o

  | red_spec_object_iter_own_prop_nil : forall S C o, 
      red_expr S C Knil o -> 
      red_expr S C (spec_object_iter_own_prop_1 nil Kprop Knil) o

  | red_spec_object_iter_own_prop_cons : forall S C A x o, 
      red_expr S C (Kprop x A (spec_iter_properties_1 L Kprop Knil)) o -> 
      red_expr S C (spec_object_iter_own_prop_1 ((x, A)::L) Kprop Knil) o
*)

  (** IsFrozen (returns bool)  (15.2.3.12) *)
    (* TODO *)
  
  (** IsExtensible (returns bool)  (15.2.3.13) *)

  | red_spec_call_object_is_extensible : forall S C v o args, 
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_is_extensible_1 v) o ->
      red_expr S C (spec_call_builtin builtin_object_is_extensible args) o
      
  | red_spec_call_object_is_extensible_1_not_object : forall S C v o, 
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_object_is_extensible_1 v) o

  | red_spec_call_object_is_extensible_1_object : forall S C l b, 
      object_extensible S l b -> 
      red_expr S C (spec_call_object_is_extensible_1 l) (out_ter S b)
  
  (** preventExtensions(O) (returns object)  (15.2.3.10) *)
  
  | red_spec_call_object_prevent_extensions : forall S C v o args,
      arguments_from args (v::nil) ->
      red_expr S C (spec_call_object_prevent_extensions_1 v) o ->
      red_expr S C (spec_call_builtin builtin_object_prevent_extensions args) o

  | red_spec_call_object_prevent_extensions_not_object : forall S C v o,  
      type_of v <> type_object ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_object_prevent_extensions_1 v) o

  | red_spec_call_object_prevent_extensions_object : forall S S' C O l, 
      object_binds S l O ->
      let O1 := object_with_extension O false in
      S' = object_write S l O1 ->
      red_expr S C (spec_call_object_prevent_extensions_1 l) (out_ter S' l)


(*------------------------------------------------------------*)
(** ** Object prototype builtin functions (15.2.3) *)

  (** Object.prototype.toString() (returns string)  (15.2.4.2) *)

  | red_spec_call_object_proto_to_string : forall S C args o, 
      red_expr S C (spec_call_object_proto_to_string_1 (execution_ctx_this_binding C)) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_to_string_call args) o

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
      red_expr S C (spec_call_builtin builtin_object_proto_value_of_call args) o 

   (** Object.prototype.isPrototypeOf() (returns bool)  (15.2.4.6) *)

   | red_spec_call_object_proto_is_prototype_of_not_object : forall S C args v o, (* Step 0 *)
      arguments_from args (v::nil)  ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v) o ->
      red_expr S C (spec_call_builtin builtin_object_proto_is_prototype_of_call args) o

   | red_spec_call_object_proto_is_prototype_of_1_not_object : forall S C v, (* Step 1 *)
      type_of v <> type_object ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v) (out_ter S false)

   | red_spec_call_object_proto_is_prototype_of_1_object : forall S C l o1 o, (* Step 2 *)
      red_expr S C (spec_to_object (execution_ctx_this_binding C)) o1 ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_2 o1 l) o ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_1 l) o

   | red_spec_call_object_proto_is_prototype_of_2 : forall S0 S C l lthis o,
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l) o ->
      red_expr S0 C (spec_call_object_proto_is_prototype_of_2_2 (out_ter S lthis) l) o

   | red_spec_call_object_proto_is_prototype_of_3 : forall S C l lthis vproto o, (* Step 3.a *)
      object_proto S l vproto -> 
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis vproto) o ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l) o

   | red_spec_call_object_proto_is_prototype_of_4_null : forall S C lthis o, (* Step 3.b *)
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis null) (out_ter S false)

   | red_spec_call_object_proto_is_prototype_of_4_equal : forall S C lthis o, (* Step 3.c *)
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis lthis) (out_ter S true)
  
   | red_spec_call_object_proto_is_prototype_of_4_not_equal : forall S C l lthis lproto o, (* Look back to step 3 *)
      (* Note: we implicitly enforce the fact that a proto can only be a location or null *)
      lproto <> lthis -> 
      red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis lproto) o ->
      red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis lproto) o

   (** Object.prototype.propertyIsEnumerable(V) (returns bool)  (15.2.4.7) *)

   | red_spec_call_object_proto_prop_is_enumerable : forall S C v o args,  
       arguments_from args (v::nil)  ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_1 v) o ->
       red_expr S C (spec_call_builtin builtin_object_proto_prop_is_enumerable args) o

   | red_spec_call_object_proto_prop_is_enumerable_1 : forall S C v o o1, 
       red_expr S C (spec_to_string v) o1 ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_2 o1) o -> 
       red_expr S C (spec_call_object_proto_prop_is_enumerable_1 v) o

   | red_spec_call_object_proto_prop_is_enumerable_2 : forall S S' C s o o1, 
       red_expr S C (spec_to_object (execution_ctx_this_binding C)) o1 ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_3 o1 s) o ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_2 (out_ter S' s)) o
       
   | red_spec_call_object_proto_prop_is_enumerable_3 : forall S S' C l x o,  
       red_expr S C (spec_object_get_own_prop l x spec_call_object_proto_prop_is_enumerable_4) o ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_3 (out_ter S' l) x) o

   | red_spec_call_object_proto_prop_is_enumerable_4_undef : forall S C, 
       red_expr S C (spec_call_object_proto_prop_is_enumerable_4 full_descriptor_undef) (out_ter S false)

   | red_spec_call_object_proto_prop_is_enumerable_4_not_undef : forall S C A b, 
       b = attributes_enumerable A ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_4 A) (out_ter S b)

  (*------------------------------------------------------------*)
  (** ** Function builtin functions *)
  
  (** Function.prototype() -- always return undefined  (15.3.4) *)

  | red_spec_call_function_proto_invoked : forall S C args,
      red_expr S C (spec_call_builtin builtin_function_proto_invoked args) (out_ter S undef)

(*---start todo---*)

  (** Get (15.3.5.4) *)

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

(** TODO: HasInstance  15.3.4.5.3 and  15.3.5.3 *)

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

(*---end todo---*)

  (*------------------------------------------------------------*)
  (** ** Array builtin functions : LATER *)

  (* TODO: special implementation of get_own_property *)

  (*------------------------------------------------------------*)
  (** ** String builtin functions : LATER *)

  (* TODO: special implementation of get_own_property *)

  (*------------------------------------------------------------*)
  (** ** Date builtin functions : LATER *)
  
  (* TODO: special hint for default_value  *)

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
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of_call args) o1 ->
      red_expr S C (spec_call_bool_proto_to_string_1 o1) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_to_string_call args) o

  | red_spec_call_bool_proto_to_string_1 : forall S0 S C s b, 
      s = (convert_bool_to_string b) ->
      red_expr S0 C (spec_call_bool_proto_to_string_1 (out_ter S b)) (out_ter S s)

  (** Boolean.prototype.valueOf() (returns bool)  (15.6.4.3) *)

  | red_spec_call_bool_proto_value_of : forall S C v o args, 
      v = execution_ctx_this_binding C ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) o ->
      red_expr S C (spec_call_builtin builtin_bool_proto_value_of_call args) o

  | red_spec_call_bool_proto_value_of_1_bool : forall S C v b,
      value_viewable_as "Boolean" S v b ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) (out_ter S b)

   | red_spec_call_bool_proto_value_of_1_not_bool : forall S C v o,
      (forall b, ~ value_viewable_as "Boolean" S v b) ->
      red_expr S C (spec_error builtin_type_error) o ->
      red_expr S C (spec_call_bool_proto_value_of_1 v) o


  (*------------------------------------------------------------*)
  (** ** Number builtin functions *)

  (** Number(value) (returns object_loc)  (15.7.1.1) *)

  | red_spec_call_number_call_nil : forall S C, 
      red_expr S C (spec_call_builtin builtin_number_call nil) (out_ter S JsNumber.zero) 

  | red_spec_call_number_call_not_nil : forall S C v o args,
      args <> nil ->
      arguments_from args (v::nil) ->
      red_expr S C (spec_to_number v) o ->
      red_expr S C (spec_call_builtin builtin_number_call args) o 

  (** new Number([value]) (returns object_loc)  (15.7.2.1) *)
  
  | red_spec_call_number_new_nil : forall S C o,
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
      red_expr S C (spec_call_builtin builtin_number_proto_value_of_call args) o

  | red_spec_call_number_proto_value_of_1_number : forall S C v n,
      value_viewable_as "Number" S v n ->
      red_expr S C (spec_call_number_proto_value_of_1 v) (out_ter S n)

   | red_spec_call_number_proto_value_of_1_not_number : forall S C v o,
      (forall n, ~ value_viewable_as "Number" S v n) ->
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
      red_expr S C (spec_call_builtin builtin_number_proto_to_string_call args) o

  (* if [this] is a number we proceed to the next stages *)
  | red_spec_call_number_proto_to_string_number : forall S C s b o v args, 
      v = execution_ctx_this_binding C ->
      type_of v = type_number -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string_call args) o

  (* The [radix] parameter is not there: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_1_no_radix : forall S C v o args, 
      args = nil ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string_call (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
      red_expr S C (spec_call_number_proto_to_string_1 v args) o 

  (* The [radix] parameter is undefined: use 10 as default *)
  | red_spec_call_number_proto_to_string_number_1_undef_radix : forall S C v vr args o, 
      arguments_from args (vr::nil) ->
      vr = undef ->
      red_expr S C (spec_call_builtin builtin_number_proto_to_string_call (value_prim (prim_number (JsNumber.of_int 10))::args)) o -> 
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
      A = attributes_data_intro JsNumber.zero false false false ->
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

------ end under dvpt --------**)

(*  | object_get_own_property_string : forall S l x An An',
      object_class S l "String" ->
      object_get_own_property_default S l x An ->
      (If An <> full_descriptor_undef
       then An' = An
       else 
         (If (prim_string x <> convert_prim_to_string (prim_number (JsNumber.absolute (convert_primitive_to_integer x)))) (* TODO: remove coercion *)
          then An' = full_descriptor_undef
          else (* TODO: make an auxiliary definition for this else branch *)
            (exists s, exists (i:int),
                 object_prim_value S l (prim_string s)
              /\ JsNumber.of_int i = convert_primitive_to_integer x
              /\ let len : int := String.length s in
                 If (len <= i)
                 then An' = full_descriptor_undef
                 else (let s' := string_sub s i 1 in
                       An' = attributes_data_intro s' false true false)
          )
      )) ->
      object_get_own_property S l x An'.
*)






