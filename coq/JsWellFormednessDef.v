Set Implicit Arguments.
Require Export JsPrettyInterm JsInit JsPrettyRules1.

(*definition of state_extends*)

(*H extends H'*)
Definition heap_extends {X Y:Type} (H H':Heap.heap X Y) : Prop :=
  forall (x:X), Heap.indom H' x -> Heap.indom H x.

(*S extends S'*)
Definition state_extends (S S':state) : Prop :=
  heap_extends (state_object_heap S) (state_object_heap S') /\
  heap_extends (state_env_record_heap S) (state_env_record_heap S').


Lemma heap_extends_refl : forall {X Y:Type} (H:Heap.heap X Y),
  heap_extends H H.
Proof.
  introv. unfolds*.
Qed.


Lemma heap_extends_trans : forall {X Y:Type} (H1 H2 H3:Heap.heap X Y),
  heap_extends H2 H1 ->
  heap_extends H3 H2 ->
  heap_extends H3 H1.
Proof.
  introv Hext1 Hext2. unfolds*.
Qed.


Lemma state_extends_refl : forall (S:state),
  state_extends S S.
Proof.
  introv. splits; apply heap_extends_refl.
Qed.


Lemma state_extends_trans : forall (S1 S2 S3:state),
  state_extends S2 S1 ->
  state_extends S3 S2 ->
  state_extends S3 S1.
Proof.
introv Hext1 Hext2. unfolds. splits; inverts Hext1; inverts Hext2; eapply heap_extends_trans; eauto.
Qed.



Inductive state_of_out : out -> state -> Prop  := 
  | state_of_out_ter : forall (S:state) (R:res),
      state_of_out (out_ter S R) S.


(*well-formedness for binary operators*)
Inductive wf_binary_op : binary_op -> Prop :=
  | wf_binary_op_mult : wf_binary_op binary_op_mult
  | wf_binary_op_div : wf_binary_op binary_op_div
  | wf_binary_op_mod : wf_binary_op binary_op_mod
  | wf_binary_op_add : wf_binary_op binary_op_add
  | wf_binary_op_sub : wf_binary_op binary_op_sub
  | wf_binary_op_left_shift : wf_binary_op binary_op_left_shift
  | wf_binary_op_right_shift : wf_binary_op binary_op_right_shift
  | wf_binary_op_unsigned_right_shift : wf_binary_op binary_op_unsigned_right_shift
  | wf_binary_op_lt : wf_binary_op binary_op_lt
  | wf_binary_op_gt : wf_binary_op binary_op_gt
  | wf_binary_op_le : wf_binary_op binary_op_le
  | wf_binary_op_ge : wf_binary_op binary_op_ge
  | wf_binary_op_instanceof : wf_binary_op binary_op_instanceof
  | wf_binary_op_in : wf_binary_op binary_op_in
  | wf_binary_op_equal : wf_binary_op binary_op_equal
  | wf_binary_op_disequal : wf_binary_op binary_op_disequal
  | wf_binary_op_strict_equal : wf_binary_op binary_op_strict_equal
  | wf_binary_op_strict_disequal : wf_binary_op binary_op_strict_disequal
  | wf_binary_op_bitwise_and : wf_binary_op binary_op_bitwise_and
  | wf_binary_op_bitwise_or : wf_binary_op binary_op_bitwise_or
  | wf_binary_op_bitwise_xor : wf_binary_op binary_op_bitwise_xor
  | wf_binary_op_and : wf_binary_op binary_op_and
  | wf_binary_op_or : wf_binary_op binary_op_or
  | wf_binary_op_coma : wf_binary_op binary_op_coma.




Inductive wf_obinary_op : option binary_op -> Prop :=
  | wf_obinary_op_none :
      wf_obinary_op None
  | wf_obinary_op_some : forall (op:binary_op),
      wf_binary_op op ->
      wf_obinary_op (Some op).


(*well-formedness for programs*)
(*the state and the strictness flag are currently unused but may be needed later*)

Inductive wf_expr (S:state) (str:strictness_flag) : expr -> Prop :=
  | wf_expr_this : wf_expr S str expr_this
  | wf_expr_identifier : forall (s:string),
      wf_expr S str (expr_identifier s)
  | wf_expr_literal : forall (i:literal),
      wf_expr S str (expr_literal i)
  | wf_expr_unary_op : forall (op:unary_op) (e:expr),
      wf_expr S str e ->
      wf_expr S str (expr_unary_op op e)
  | wf_expr_binary_op : forall (op:binary_op) (e1 e2:expr),
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_binary_op op ->
      wf_expr S str (expr_binary_op e1 op e2)
  | wf_expr_conditional : forall (e1 e2 e3 : expr),
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_expr S str e3 ->
      wf_expr S str (expr_conditional e1 e2 e3)
  | wf_expr_assign : forall (e1 e2:expr) (oop:option binary_op),
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_obinary_op oop ->
      wf_expr S str (expr_assign e1 oop e2).


Inductive wf_oexpr (S:state) (str:strictness_flag) : option expr -> Prop :=
  | wf_oexpr_none : wf_oexpr S str None
  | wf_oexpr_some : forall (e:expr),
      wf_expr S str e ->
      wf_oexpr S str (Some e).


Inductive wf_var_decl (S:state) (str:strictness_flag) : string*option expr -> Prop :=
  | wf_var_decl_none : forall (s:string),
      wf_var_decl S str (s,None)
  | wf_var_decl_some : forall (s:string) (e:expr),
      wf_expr S str e ->
      wf_var_decl S str (s,Some e).


Inductive wf_stat (S:state) (str:strictness_flag) : stat -> Prop :=
  | wf_stat_expr : forall (e:expr),
      wf_expr S str e ->
      wf_stat S str (stat_expr e)
  | wf_stat_label : forall (s:string) (t:stat),
      wf_stat S str t ->
      wf_stat S str (stat_label s t)
  | wf_stat_block_nil :(*not elegant :( but I need this for the recursion in wf_stat_state_extends*)
      wf_stat S str (stat_block nil)
  | wf_stat_block_cons : forall (t:stat) (lt:list stat),
      wf_stat S str t ->
      wf_stat S str (stat_block lt) ->
      wf_stat S str (stat_block (lt&t))
  | wf_stat_var_decl : forall (l:list (string*option expr)),
      Forall (wf_var_decl S str) l ->
      wf_stat S str (stat_var_decl l)
  | wf_stat_if_none : forall (e:expr) (t:stat),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_stat S str (stat_if e t None)
  | wf_stat_if_some : forall (e:expr) (t t':stat),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_stat S str t' ->
      wf_stat S str (stat_if e t (Some t'))
  | wf_stat_do_while : forall (ls:label_set) (t:stat) (e:expr),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_stat S str (stat_do_while ls t e)
  | wf_stat_while : forall (ls:label_set) (e:expr) (t:stat),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_stat S str (stat_while ls e t)
  | wf_stat_with : forall (e:expr) (t:stat),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_stat S str (stat_with e t)
  | wf_stat_throw : forall (e:expr),
      wf_expr S str e ->
      wf_stat S str (stat_throw e)
  | wf_stat_return : forall (oe:option expr),
      wf_oexpr S str oe ->
      wf_stat S str (stat_return oe)
  | wf_stat_break : forall (lab:label),
      wf_stat S str (stat_break lab)
  | wf_stat_continue : forall (lab:label),
      wf_stat S str (stat_continue lab)
  | wf_stat_try : forall (t:stat),
      wf_stat S str t ->
      wf_stat S str (stat_try t None None)
  | wf_stat_trycatch : forall (t1 t2 :stat) (s:string),
      wf_stat S str t1 ->
      wf_stat S str t2 ->
      wf_stat S str (stat_try t1 (Some (s,t2)) None)
  | wf_stat_tryfinally : forall (t1 t2:stat),
      wf_stat S str t1 ->
      wf_stat S str t2 ->
      wf_stat S str (stat_try t1 None (Some t2))
  | wf_stat_trycatchfinally : forall (t1 t2 t3:stat) (s:string),
      wf_stat S str t1 ->
      wf_stat S str t2 ->
      wf_stat S str t3 ->
      wf_stat S str (stat_try t1 (Some (s,t2)) (Some t3))
  | wf_stat_for : forall (labs:label_set) (oe1 oe2 oe3:option expr) (t:stat),
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_oexpr S str oe3 ->
      wf_stat S str t ->
      wf_stat S str (stat_for labs oe1 oe2 oe3 t)
  | wf_stat_for_var : forall (labs:label_set) (l:list (string*option expr)) (oe1 oe2:option expr) (t:stat),
      Forall (wf_var_decl S str) l ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_stat S str (stat_for_var labs l oe1 oe2 t).


Inductive wf_ostat (S:state) (str:strictness_flag) : (option stat) -> Prop :=
  | wf_ostat_none : wf_ostat S str None
  | wf_ostat_some : forall (t:stat),
      wf_stat S str t ->
      wf_ostat S str (Some t).


Inductive wf_ostringstat (S:state) (str:strictness_flag) : (option (string * stat)) -> Prop :=
  | wf_ostringstat_none : wf_ostringstat S str None
  | wf_ostringstat_some : forall (s:string) (t:stat),
      wf_stat S str t ->
      wf_ostringstat S str (Some (s,t)).



Inductive wf_element (S:state) (str:strictness_flag) : element -> Prop :=
  | wf_element_stat : forall (t:stat),
      wf_stat S str t ->
      wf_element S str (element_stat t).


Inductive wf_prog (S:state) (str:strictness_flag): prog -> Prop :=
  | wf_prog_intro : forall (l:list element),
      Forall (wf_element S str) l ->
      wf_prog S str (prog_intro str l).

Definition  wf_object_loc (S:state) (str:strictness_flag) (l:object_loc) : Prop :=
  object_indom S l.

Inductive wf_value (S:state) (str:strictness_flag) : value -> Prop :=
  | wf_value_prim : forall (w:prim),
      wf_value S str (value_prim w)
  | wf_value_object : forall (l:object_loc),
      object_indom S l ->
      wf_value S str (value_object l).

Inductive wf_ovalue (S:state) (str:strictness_flag) : option value -> Prop :=
  | wf_ovalue_none :
      wf_ovalue S str None
  | wf_ovalue_some : forall (v:value),
      wf_value S str v ->
      wf_ovalue S str (Some v).




(*well-formedness for env_records*)

Definition wf_decl_env_record (S:state) (str:strictness_flag) (env:decl_env_record) : Prop :=
  forall (s:string) (m:mutability) (v:value),
    decl_env_record_binds env s m v ->
    wf_value S str v.


Inductive wf_env_record (S:state) (str:strictness_flag) : env_record -> Prop :=
  | wf_env_record_decl : forall (env:decl_env_record),
      wf_decl_env_record S str env ->
      wf_env_record S str (env_record_decl env)
  | wf_env_record_object : forall (l:object_loc) (f:provide_this_flag),
      wf_object_loc S str l ->
      wf_env_record S str (env_record_object l f).




(*well-formedness for env_loc*)
(*check that the env_loc is bound to some env_record in the state*)
Inductive wf_env_loc (S:state) (str:strictness_flag) : env_loc -> Prop :=
  | wf_env_loc_bound : forall (L:env_loc),
      Heap.indom (state_env_record_heap S) L ->
      wf_env_loc S str L.




(*well-formedness for descriptors*)
(*the descriptor has to has get and set to None*)
Inductive wf_descriptor (S:state) (str:strictness_flag) : descriptor -> Prop :=
  | wf_descriptor_intro : forall (ov1:option value) (ob1 ob2 ob3:option bool),
      wf_ovalue S str ov1 ->
      wf_descriptor S str (descriptor_intro ov1 ob1 None None ob2 ob3).




(*well-formedness for attributes*)
(*only data attributes are well-formed*)
Inductive wf_attributes (S:state) (str:strictness_flag) : attributes -> Prop :=
  | wf_attributes_data_of : forall (v:value) (b1 b2 b3:bool),
      wf_value S str v ->
      wf_attributes S str (attributes_data_of (attributes_data_intro v b1 b2 b3)).
(*  | wf_attributes_accessor_of : forall (v v':value) (b b':bool),
      wf_value S str v ->
      wf_value S str v' ->
      wf_attributes S str (attributes_accessor_of (attributes_accessor_intro v v' b b')).*)


Inductive wf_oattributes (S:state) (str:strictness_flag) : option attributes -> Prop :=
  | wf_oattributes_none :
      wf_oattributes S str None
  | wf_oattributes_some : forall (A:attributes),
      wf_attributes S str A ->
      wf_oattributes S str (Some A).


Inductive wf_full_descriptor (S:state) (str:strictness_flag) : full_descriptor -> Prop :=
  | wf_full_descriptor_undef : wf_full_descriptor S str full_descriptor_undef
  | wf_full_descriptor_some : forall (A:attributes),
      wf_attributes S str A ->
      wf_full_descriptor S str (full_descriptor_some A).




(*well-formedness for objects*)
Record wf_object (S:state) (str:strictness_flag) (obj:object) :=
  wf_object_intro {
    wf_object_proto_ : wf_value S str (object_proto_ obj);
    wf_object_define_own_prop : object_define_own_prop_ obj = builtin_define_own_prop_default;
    wf_object_get_own_prop : object_get_own_prop_ obj = builtin_get_own_prop_default;
    wf_object_properties : forall (x:prop_name) (A:attributes),
      Heap.binds (object_properties_ obj) x A ->
      wf_attributes S str A}.




(*well-formedness for states*)

Record wf_state_prealloc_global_aux (S:state) (obj:object) := wf_state_prealloc_global_aux_intro {
  wf_state_prealloc_global_binds :
    Heap.binds (state_object_heap S) (object_loc_prealloc prealloc_global) obj;
  wf_state_prealloc_global_define_own_prop :
    object_define_own_prop_ obj = builtin_define_own_prop_default;
  wf_state_prealloc_global_get :
    object_get_ obj = builtin_get_default;
  wf_state_prealloc_global_get_own_prop :
     object_get_own_prop_ obj = builtin_get_own_prop_default}.
                                    

Record wf_state (S:state) := wf_state_intro {
  wf_state_wf_objects : (forall (obj:object) (str:strictness_flag),
    (exists (l:object_loc), object_binds S l obj) ->
    wf_object S str obj);
  wf_state_prealloc_global :
    exists obj, wf_state_prealloc_global_aux S obj;
  wf_state_prealloc_native_error_proto : forall (ne:native_error),
    object_indom S (prealloc_native_error_proto ne);
  wf_state_wf_env_records : forall (E:env_record) (str:strictness_flag),
    (exists (L:env_loc), env_record_binds S L E) ->
    wf_env_record S str E;
  wf_state_env_loc_global_env_record :
    Heap.indom (state_env_record_heap S) env_loc_global_env_record}.




(*well-formedness for execution contexts (scope chains)*)


Inductive wf_lexical_env (S:state) (str:strictness_flag) : lexical_env -> Prop :=
  | wf_lexical_env_nil : wf_lexical_env S str nil
  | wf_lexical_env_cons : forall (L:env_loc) (lex:lexical_env),
      wf_env_loc S str L ->
      wf_lexical_env S str lex ->
      wf_lexical_env S str (L::lex).

Definition only_global_scope (C:execution_ctx) :=
  execution_ctx_lexical_env C = (env_loc_global_env_record::nil). (*maybe too strict*)


Record wf_execution_ctx (S:state) (str:strictness_flag) (C:execution_ctx) := wf_execution_ctx_intro {
  wf_execution_ctx_wf_lexical_env : wf_lexical_env S str (execution_ctx_lexical_env C);
  wf_execution_ctx_wf_variable_env : wf_lexical_env S str (execution_ctx_variable_env C); 
  wf_execution_ctx_this_binding : wf_value S str (execution_ctx_this_binding C)}.
  (*wf_execution_ctx_only_global_scope : only_global_scope C}.*)





(*well-formedness for out*)

Inductive wf_ref_base_type (S:state) (str:strictness_flag) : ref_base_type -> Prop :=
  | wf_ref_base_type_value : forall (v:value),
      wf_value S str v ->
      wf_ref_base_type S str (ref_base_type_value v)
  | wf_ref_base_type_env_loc : forall (L:env_loc),
      wf_env_loc S str L ->
      wf_ref_base_type S str (ref_base_type_env_loc L).


Inductive wf_ref (S:state) (str:strictness_flag) : ref -> Prop :=
  | wf_ref_intro : forall (rbase:ref_base_type) (x:prop_name) (b:bool),
      wf_ref_base_type S str rbase ->
      wf_ref S str (ref_intro rbase x b).


Inductive wf_resvalue (S:state) (str:strictness_flag) : resvalue -> Prop :=
  | wf_resvalue_empty : wf_resvalue S str resvalue_empty
  | wf_resvalue_value : forall v:value,
      wf_value S str v ->
      wf_resvalue S str (resvalue_value v)
  | wf_resvalue_ref : forall r:ref,
      wf_ref S str r ->
      wf_resvalue S str (resvalue_ref r).


Inductive wf_restype : restype -> Prop :=
  | wf_restype_normal : wf_restype restype_normal
  | wf_restype_break : wf_restype restype_break
  | wf_restype_continue : wf_restype restype_continue
  | wf_restype_return : wf_restype restype_return
  | wf_restype_throw : wf_restype restype_throw.


Inductive wf_res (S:state) (str:strictness_flag) : res -> Prop :=
  | wf_res_intro : forall (rt:restype) (rv:resvalue) (lab:label), (*not sure about the label and the type*)
      wf_restype rt ->
      wf_resvalue S str rv ->
      wf_res S str (res_intro rt rv lab).


Inductive wf_out (S:state) (str:strictness_flag) : out -> Prop :=
(*  | wf_out_div : wf_out S str out_div*) (*shouldn't happen actually*)
  | wf_out_ter : forall (S':state) (R:res),
      wf_state S' ->
      state_extends S' S ->
      wf_res S' str R ->
      wf_out S str (out_ter S' R).





(*well-formedness for intermediate forms*)
Inductive wf_specval (S:state) (str:strictness_flag) : specval -> Prop :=
  | wf_specval_void : wf_specval S str specval_void
  | wf_specval_value : forall (v:value),
      wf_value S str v ->
      wf_specval S str (specval_value v)
  | wf_specval_value2 : forall (v1 v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_specval S str (specval_value2 (v1,v2))
  | wf_specval_int : forall (i:int),
      wf_specval S str (specval_int i)
  | wf_specval_ref : forall (r:ref),
      wf_ref S str r ->
      wf_specval S str (specval_ref r)
  | wf_specval_full_descriptor : forall (D:full_descriptor),
      wf_full_descriptor S str D ->
      wf_specval S str (specval_full_descriptor D)
  | wf_specval_attributes : forall (A:attributes),
      wf_attributes S str A ->
      wf_specval S str (specval_attributes A)
  | wf_specval_descriptor : forall (Desc:descriptor),
      wf_descriptor S str Desc ->
      wf_specval S str (specval_descriptor Desc)
  | wf_specval_listvalue : forall (l:listvalue),
      Forall (wf_value S str) l ->
      wf_specval S str (specval_listvalue l).


Inductive wf_specret (S:state) (str:strictness_flag) : specret -> Prop :=
  | wf_specret_out : forall (o:out),
      wf_out S str o ->
      wf_specret S str (specret_out o)
  | wf_specret_val : forall (t:specval) (S':state),
      wf_state S' ->
      wf_specval S' str t ->
      state_extends S' S ->
      wf_specret S str (specret_val S' t).




Inductive wf_ext_prog (S:state) (str:strictness_flag) : ext_prog -> Prop :=
  | wf_prog_basic : forall (p:prog),
      wf_prog S str p ->
      wf_ext_prog S str (prog_basic p)
  | wf_javascript_1 : forall (S':state) (o:out) (p:prog),
      wf_out S str o ->
      state_of_out o S' -> 
      wf_prog S' str p ->
      wf_ext_prog S str (javascript_1 o p)
  | wf_prog_1 : forall (S':state) (o:out) (el:element),
      wf_out S str o ->
      state_of_out o S' ->
      wf_element S' str el ->
      wf_ext_prog S str (prog_1 o el)
  | wf_prog_2 : forall (rv:resvalue) (o:out),
      wf_resvalue S str rv ->
      wf_out S str o ->
      wf_ext_prog S str (prog_2 rv o).




Inductive wf_ext_stat (S:state) (str:strictness_flag) : ext_stat -> Prop :=
  (*stat_basic*)
  | wf_stat_basic : forall (t:stat),
      wf_stat S str t ->
      wf_ext_stat S str (stat_basic t)
  (*stat_expr*)
  | wf_stat_expr_1 : forall (sv:specret),
      wf_specret S str sv ->
      wf_ext_stat S str (stat_expr_1 sv)
  (*stat_block*)
  | wf_stat_block_1 : forall (o:out) (t:stat),
      wf_out S str o ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_block_1 o t)
  | wf_stat_block_2 : forall (rv:resvalue) (o:out),
      wf_resvalue S str rv ->
      wf_out S str o ->
      wf_ext_stat S str (stat_block_2 rv o)
  (*stat_label*)
  | wf_stat_label_1 : forall (lab:label) (o:out),
      wf_out S str o ->
      wf_ext_stat S str (stat_label_1 lab o)
  (*stat_var_decl*)
  | wf_stat_var_decl_1 : forall (S':state) (o:out) (l:list (string*option expr)),
      wf_out S str o ->
      state_of_out o S' ->
      Forall (wf_var_decl S' str) l ->
      wf_ext_stat S str (stat_var_decl_1 o l)
  | wf_stat_var_decl_item : forall (d:string*option expr),
      wf_var_decl S str d ->
      wf_ext_stat S str (stat_var_decl_item d)
  | wf_stat_var_decl_item_1 : forall (s:string) (sr:specret) (e:expr),
      wf_specret S str sr ->
      wf_expr S str e ->
      wf_ext_stat S str (stat_var_decl_item_1 s sr e)
  | wf_stat_var_decl_item_2 : forall (s:string) (r:ref) (sv:specret),
      wf_ref S str r ->
      wf_specret S str sv ->
      wf_ext_stat S str (stat_var_decl_item_2 s r sv)
  | wf_stat_var_decl_item_3 : forall (s:string) (o:out),
      wf_out S str o ->
      wf_ext_stat S str (stat_var_decl_item_3 s o)
  (*stat_if*)
  | wf_stat_if_1_none : forall (y:specret) (t:stat),
      wf_specret S str y ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_if_1 y t None)
  | wf_stat_if_1_some : forall (y:specret) (t t':stat),
      wf_specret S str y ->
      wf_stat S str t ->
      wf_stat S str t' ->
      wf_ext_stat S str (stat_if_1 y t (Some t'))
  (*stat_while*)
  | wf_stat_while_1 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_ext_stat S str (stat_while_1 labs e t rv)
  | wf_stat_while_2 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue) (y:specret),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_specret S str y ->
      wf_ext_stat S str (stat_while_2 labs e t rv y)
  | wf_stat_while_3 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue) (o:out),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_out S str o ->
      wf_ext_stat S str (stat_while_3 labs e t rv o)
  | wf_stat_while_4 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue) (R:res),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_while_4 labs e t rv R)
  | wf_stat_while_5 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue) (R:res),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_while_5 labs e t rv R)
  | wf_stat_while_6 : forall (labs:label_set) (e:expr) (t:stat) (rv:resvalue) (R:res),
      wf_expr S str e ->
      wf_stat S str t ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_while_6 labs e t rv R)
  (*stat_do_while*)
  | wf_stat_do_while_1 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_ext_stat S str (stat_do_while_1 labs t e rv)
  | wf_stat_do_while_2 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue) (o:out),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_out S str o ->
      wf_ext_stat S str (stat_do_while_2 labs t e rv o)
  | wf_stat_do_while_3 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue) (R:res),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_do_while_3 labs t e rv R)
  | wf_stat_do_while_4 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue) (R:res),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_do_while_4 labs t e rv R)
  | wf_stat_do_while_5 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue) (R:res),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_res S str R ->
      wf_ext_stat S str (stat_do_while_5 labs t e rv R)
  | wf_stat_do_while_6 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_ext_stat S str (stat_do_while_6 labs t e rv)
  | wf_stat_do_while_7 : forall (labs:label_set) (t:stat) (e:expr) (rv:resvalue) (y:specret),
      wf_stat S str t ->
      wf_expr S str e ->
      wf_resvalue S str rv ->
      wf_specret S str y ->
      wf_ext_stat S str (stat_do_while_7 labs t e rv y)
  (*stat_for*)
  | wf_stat_for_1 : forall (labs:label_set) (y:specret) (oe1 oe2:option expr) (t:stat),
      wf_specret S str y ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_1 labs y oe1 oe2 t)
  | wf_stat_for_2 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (t:stat),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_2 labs rv oe1 oe2 t)
  | wf_stat_for_3 : forall (labs:label_set) (rv:resvalue) (e:expr) (y:specret) (oe:option expr) (t:stat),
      wf_resvalue S str rv ->
      wf_expr S str e ->
      wf_specret S str y ->
      wf_oexpr S str oe ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_3 labs rv e y oe t)
  | wf_stat_for_4 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (t:stat),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_4 labs rv oe1 oe2 t)
  | wf_stat_for_5 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (o:out) (t:stat),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_out S str o ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_5 labs rv oe1 o oe2 t)
  | wf_stat_for_6 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (t:stat) (R:res),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_res S str R ->
      wf_ext_stat S str (stat_for_6 labs rv oe1 oe2 t R)
  | wf_stat_for_7 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (t:stat) (R:res),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_res S str R ->
      wf_ext_stat S str (stat_for_7 labs rv oe1 oe2 t R)
  | wf_stat_for_8 : forall (labs:label_set) (rv:resvalue) (oe1 oe2:option expr) (t:stat),
      wf_resvalue S str rv ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_8 labs rv oe1 oe2 t)
  | wf_stat_for_9 : forall (labs:label_set) (rv:resvalue) (oe:option expr) (e:expr) (y:specret) (t:stat),
      wf_resvalue S str rv ->
      wf_oexpr S str oe ->
      wf_expr S str e ->
      wf_specret S str y ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_9 labs rv oe e y t)
  | wf_stat_for_var_1 : forall (o:out) (labs:label_set) (oe1 oe2:option expr) (t:stat),
      wf_out S str o ->
      wf_oexpr S str oe1 ->
      wf_oexpr S str oe2 ->
      wf_stat S str t ->
      wf_ext_stat S str (stat_for_var_1 o labs oe1 oe2 t)
  (*stat_with*)
  | wf_stat_with_1 : forall (t:stat) (y:specret),
      wf_stat S str t ->
      wf_specret S str y ->
      wf_ext_stat S str (stat_with_1 t y)
  (*stat_throw*)
  | wf_stat_throw_1 : forall (y:specret),
      wf_specret S str y ->
      wf_ext_stat  S str (stat_throw_1 y)
  (*stat_return*)
  | wf_stat_return_1 : forall (y:specret),
      wf_specret S str y ->
      wf_ext_stat S str (stat_return_1 y)
  (*stat_try*)
  | wf_stat_try_1 : forall (o:out) (ost:option (string*stat)) (ot:option stat),
      wf_out S str o ->
      wf_ostringstat S str ost ->
      wf_ostat S str ot ->
      wf_ext_stat S str (stat_try_1 o ost ot)
  | wf_stat_try_2 : forall (o:out) (lex:lexical_env) (t:stat) (ot:option stat),
      wf_out S str o ->
      wf_lexical_env S str lex ->
      wf_stat S str t ->
      wf_ostat S str ot ->
      wf_ext_stat S str (stat_try_2 o lex t ot)
  | wf_stat_try_3 : forall (o:out) (ot:option stat),
      wf_out S str o ->
      wf_ostat S str ot ->
      wf_ext_stat S str (stat_try_3 o ot)
  | wf_stat_try_4 : forall (R:res) (ot:option stat),
      wf_res S str R ->
      wf_ostat S str ot ->
      wf_ext_stat S str (stat_try_4 R ot)
  | wf_stat_try_5 : forall (R:res) (o:out),
      wf_res S str R ->
      wf_out S str o ->
      wf_ext_stat S str (stat_try_5 R o).


Inductive wf_ext_expr (S:state) (str:strictness_flag) : ext_expr -> Prop :=
  | wf_expr_basic : forall e:expr,
      wf_expr S str e ->
      wf_ext_expr S str (expr_basic e)
  | wf_expr_identifier_1 : forall sr:specret,
      wf_specret S str sr ->
      wf_ext_expr S str (expr_identifier_1 sr)
  | wf_expr_unary_op_1 : forall (op:unary_op) (sv:specret),
      wf_specret S str sv ->
      wf_ext_expr S str (expr_unary_op_1 op sv)
  | wf_expr_unary_op_2 : forall (op:unary_op) (v:value),
      wf_value S str v ->
      wf_ext_expr S str (expr_unary_op_2 op v)
  | wf_expr_delete_1 : forall (o:out), 
      wf_out S str o ->
      wf_ext_expr S str (expr_delete_1 o)
  | wf_expr_delete_2 : forall (r:ref),
      wf_ref S str r ->
      wf_ext_expr S str (expr_delete_2 r)
  | wf_expr_delete_3 : forall (r:ref) (o:out),
      wf_ref S str r ->
      wf_out S str o ->
      wf_ext_expr S str (expr_delete_3 r o)
  | wf_expr_delete_4 : forall (r:ref) (L:env_loc),
      wf_ref S str r ->
      wf_env_loc S str L ->
      wf_ext_expr S str (expr_delete_4 r L)
  | wf_expr_typeof_1 : forall o:out,
      wf_out S str o ->
      wf_ext_expr S str (expr_typeof_1 o)
  | wf_expr_typeof_2 : forall (sv:specret),
      wf_specret S str sv ->
      wf_ext_expr S str (expr_typeof_2 sv)
  | wf_expr_prepost_1 : forall (op:unary_op) (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_prepost_1 op o)
  | wf_expr_prepost_2 : forall (op:unary_op) (R:res) (sv:specret),
      wf_res S str R ->
      wf_specret S str sv ->
      wf_ext_expr S str (expr_prepost_2 op R sv)
  | wf_expr_prepost_3 : forall (op:unary_op) (R:res) (o:out),
      wf_res S str R ->
      wf_out S str o ->
      wf_ext_expr S str (expr_prepost_3 op R o)
  | wf_expr_prepost_4 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (expr_prepost_4 v o)
  | wf_expr_unary_op_neg_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_unary_op_neg_1 o)
  | wf_expr_unary_op_bitwise_not_1 : forall (si:specret),
      wf_specret S str si ->
      wf_ext_expr S str (expr_unary_op_bitwise_not_1 si)
  | wf_expr_unary_op_not_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_unary_op_not_1 o)
  | wf_expr_conditional_1 : forall (sv:specret) (e1 e2:expr),
      wf_specret S str sv ->
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_ext_expr S str (expr_conditional_1 sv e1 e2)
  | wf_expr_conditional_1': forall (o:out) (e1 e2:expr),
      wf_out S str o ->
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_ext_expr S str (expr_conditional_1' o e1 e2)
  | wf_expr_conditional_2 : forall (sv:specret),
      wf_specret S str sv ->
      wf_ext_expr S str (expr_conditional_2 sv)
  | wf_expr_binary_op_1 : forall (op:binary_op) (sv:specret) (e:expr),
      wf_specret S str sv ->
      wf_expr S str e ->
      wf_binary_op op ->
      wf_ext_expr S str (expr_binary_op_1 op sv e)
  | wf_expr_binary_op_2 : forall (op:binary_op) (v:value) (sv:specret),
      wf_value S str v ->
      wf_specret S str sv ->
      wf_binary_op op ->
      wf_ext_expr S str (expr_binary_op_2 op v sv)
  | wf_expr_binary_op_3 : forall (op:binary_op) (v1:value) (v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_binary_op op ->
      wf_ext_expr S str (expr_binary_op_3 op v1 v2)
  | wf_expr_binary_op_add_1 : forall (svv:specret),
      wf_specret S str svv ->
      wf_ext_expr S str (expr_binary_op_add_1 svv)
  | wf_expr_binary_op_add_string_1 : forall (svv:specret),
      wf_specret S str svv ->
      wf_ext_expr S str (expr_binary_op_add_string_1 svv)
  | wf_expr_puremath_op_1 : forall (f:(number -> number -> number)) (svv:specret),
      wf_specret S str svv ->
      wf_ext_expr S str (expr_puremath_op_1 f svv)
  | wf_expr_shift_op_1 : forall (f:int -> int -> int) (si:specret) (v:value),
      wf_specret S str si ->
      wf_value S str v ->
      wf_ext_expr S str (expr_shift_op_1 f si v)
  | wf_expr_shift_op_2 : forall (f:int -> int -> int) (k:int) (si:specret),
      wf_specret S str si ->
      wf_ext_expr S str (expr_shift_op_2 f k si)
  | wf_expr_inequality_op_1 : forall (b1 b2:bool) (v1 v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (expr_inequality_op_1 b1 b2 v1 v2)
  | wf_expr_inequality_op_2 : forall (b1 b2:bool) (svv:specret),
      wf_specret S str svv ->
      wf_ext_expr S str (expr_inequality_op_2 b1 b2 svv)
  | wf_expr_binary_op_in_1 : forall (l:object_loc) (o:out),
      wf_object_loc S str l ->
      wf_out S str o ->
      wf_ext_expr S str (expr_binary_op_in_1 l o)
  | wf_expr_binary_op_disequal_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_binary_op_disequal_1 o)
  | wf_spec_equal : forall (v1 v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (spec_equal v1 v2)
  | wf_spec_equal_1 : forall (T1 T2:type) (v1 v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (spec_equal_1 T1 T2 v1 v2)
  | wf_spec_equal_2 : forall (b:bool),
      wf_ext_expr S str (spec_equal_2 b)
  | wf_spec_equal_3 : forall (v1:value) (f:value -> ext_expr) (v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (f v2) ->
      wf_ext_expr S str (spec_equal_3 v1 f v2)
  | wf_spec_equal_4 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (spec_equal_4 v o)
  | wf_expr_bitwise_op_1 : forall (f:int -> int -> int) (si:specret) (v:value),
      wf_specret S str si ->
      wf_value S str v ->
      wf_ext_expr S str (expr_bitwise_op_1 f si v)
  | wf_expr_bitwise_op_2 : forall (f:int -> int -> int) (k:int) (si:specret),
      wf_specret S str si ->
      wf_ext_expr S str (expr_bitwise_op_2 f k si)
  | wf_expr_lazy_op_1 : forall (b:bool) (sv:specret) (e:expr),
      wf_specret S str sv ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_lazy_op_1 b sv e)
  | wf_expr_lazy_op_2 : forall (b:bool) (v:value) (o:out) (e:expr),
      wf_value S str v ->
      wf_out S str o ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_lazy_op_2 b v o e)
  | wf_expr_lazy_op_2_1 : forall (sv:specret),
      wf_specret S str sv ->
      wf_ext_expr S str (expr_lazy_op_2_1 sv)
  | wf_expr_assign_1 : forall (o:out) (oop:option binary_op) (e:expr),
      wf_out S str o ->
      wf_expr S str e ->
      wf_obinary_op oop ->
      wf_ext_expr S str (expr_assign_1 o oop e)
  | wf_expr_assign_2 : forall (R:res) (sv:specret) (op:binary_op) (e:expr),
      wf_res S str R ->
      wf_specret S str sv ->
      wf_expr S str e ->
      wf_binary_op op ->
      wf_ext_expr S str (expr_assign_2 R sv op e)
  | wf_expr_assign_3 : forall (R:res) (v:value) (op:binary_op) (sv:specret),
      wf_res S str R ->
      wf_value S str v ->
      wf_specret S str sv ->
      wf_binary_op op ->
      wf_ext_expr S str (expr_assign_3 R v op sv)
  | wf_expr_assign_3' : forall (R:res) (o:out),
      wf_res S str R ->
      wf_out S str o ->
      wf_ext_expr S str (expr_assign_3' R o)
  | wf_expr_assign_4 : forall (R:res) (sv:specret),
      wf_res S str R ->
      wf_specret S str sv ->
      wf_ext_expr S str (expr_assign_4 R sv)
  | wf_expr_assign_5 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (expr_assign_5 v o)
  (*spec_binding_inst_var_decl*)
  | wf_spec_binding_inst_var_decls : forall (L:env_loc) (ls:list string) (b:bool) (str':strictness_flag),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_var_decls L ls b str')
  | wf_spec_binding_inst_var_decls_1 : forall (L:env_loc) (s:string) (ls:list string) (b:bool) (str':strictness_flag) (o:out),
      wf_env_loc S str L ->
      wf_out S str o ->
      wf_ext_expr S str (spec_binding_inst_var_decls_1 L s ls b str' o)
  | wf_spec_binding_inst_var_decls_2 : forall (L:env_loc) (ls:list string) (b:bool) (str':strictness_flag) (o:out),
      wf_env_loc S str L ->
      wf_out S str o ->
      wf_ext_expr S str (spec_binding_inst_var_decls_2 L ls b str' o)
  (*spec_binding_inst_function_decls*)
  | wf_spec_binding_inst_function_decls : forall (L:env_loc) (str':strictness_flag) (b:bool),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_function_decls nil L nil str' b)
  (*spec_binding_inst*)
  | wf_spec_binding_inst : forall (p:prog), (*probably too strict, but I needed this*)
      wf_prog S str p ->
      wf_ext_expr S str (spec_binding_inst codetype_global None p nil)
  | wf_spec_binding_inst_1 : forall (p:prog) (L:env_loc),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_1 codetype_global None p nil L)
  | wf_spec_binding_inst_3 : forall (p:prog) (L:env_loc),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_3 codetype_global None p nil nil L)
  | wf_spec_binding_inst_4 : forall (p:prog) (L:env_loc) (b:bool) (o:out),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_out S str o ->
      wf_ext_expr S str (spec_binding_inst_4 codetype_global None p nil nil b L o)
  | wf_spec_binding_inst_5 : forall (p:prog) (L:env_loc) (b:bool),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_5 codetype_global None p nil nil b L)
  | wf_spec_binding_inst_6 : forall (p:prog) (L:env_loc) (b:bool) (o:out),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_out S str o ->
      wf_ext_expr S str (spec_binding_inst_6 codetype_global None p nil nil b L o)
  | wf_spec_binding_inst_7 : forall (p:prog) (b:bool) (L:env_loc) (o:out),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_out S str o ->
      wf_ext_expr S str (spec_binding_inst_7 p b L o)
  | wf_spec_binding_inst_8 : forall (p:prog) (b:bool) (L:env_loc),
      wf_prog S str p ->
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_binding_inst_8 p b L)
  (*spec_*_has_instance*)
  | wf_spec_object_has_instance : forall (l:object_loc) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_expr S str (spec_object_has_instance l v)
  | wf_spec_object_has_instance_1 : forall (B:builtin_has_instance) (l:object_loc) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_expr S str (spec_object_has_instance_1 B l v)
  | wf_spec_function_has_instance_1 : forall (l:object_loc) (o:out),
      wf_object_loc S str l ->
      wf_out S str o ->
      wf_ext_expr S str (spec_function_has_instance_1 l o)
  | wf_spec_function_has_instance_2 : forall (l l':object_loc),
      wf_object_loc S str l ->
      wf_object_loc S str l' ->
      wf_ext_expr S str (spec_function_has_instance_2 l l')
  | wf_spec_function_has_instance_3 : forall (l:object_loc) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_expr S str (spec_function_has_instance_3 l v)

  (*spec_error*)
  | wf_spec_error : forall (n:native_error),
      wf_ext_expr S str (spec_error n)
  | wf_spec_error_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_error_1 o)
  | wf_spec_error_or_cst : forall (b:bool) (err:native_error) (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_error_or_cst b err v)
  | wf_spec_error_or_void : forall (b:bool) (err:native_error),
      wf_ext_expr S str (spec_error_or_void b err)

  (*spec_build_error*)
  | wf_spec_build_error : forall (v:value) (v':value),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_expr S str (spec_build_error v v')
  | wf_spec_build_error_1 : forall (l:object_loc) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_expr S str (spec_build_error_1 l v)
  | wf_spec_build_error_2 : forall (l:object_loc) (o:out),
      wf_object_loc S str l ->
      wf_out S str o ->
      wf_ext_expr S str (spec_build_error_2 l o)

  | wf_spec_put_value : forall (rv:resvalue) (v:value),
      wf_resvalue S str rv ->
      wf_value S str v ->
      wf_ext_expr S str (spec_put_value rv v)
  | wf_spec_to_primitive : forall (v:value) (opt:option preftype),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_primitive v opt)
  | wf_spec_to_boolean : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_boolean v)
  | wf_spec_to_number : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_number v)
  | wf_spec_to_number_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_to_number_1 o)
  | wf_spec_to_integer : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_integer v)
  | wf_spec_to_integer_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_to_integer_1 o)
  | wf_spec_to_string : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_string v)
  | wf_spec_to_string_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_to_string_1 o)
  | wf_spec_to_object : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_to_object v)
  | wf_spec_check_object_coercible : forall (v:value),
      wf_value S str v ->
      wf_ext_expr S str (spec_check_object_coercible v)
  | wf_spec_object_delete : forall (l:object_loc) (x:prop_name) (b:bool),
      wf_ext_expr S str (spec_object_delete l x b)
  | wf_spec_object_delete_1 : forall (bdel:builtin_delete) (l:object_loc) (x:prop_name) (b:bool),
      wf_ext_expr S str (spec_object_delete_1 bdel l x b)
  | wf_spec_object_delete_2 : forall (l:object_loc) (x:prop_name) (b:bool) (sD:specret),
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_delete_2 l x b sD)
  | wf_spec_object_delete_3 : forall (l:object_loc) (x:prop_name) (b:bool) (b':bool),
      wf_ext_expr S str (spec_object_delete_3 l x b b')
  | wf_spec_env_record_has_binding : forall (L:env_loc) (x:prop_name),
      wf_ext_expr S str (spec_env_record_has_binding L x)
  | wf_spec_env_record_has_binding_1 : forall (L:env_loc) (x:prop_name) (E:env_record),
      wf_env_record S str E ->
      wf_ext_expr S str (spec_env_record_has_binding_1 L x E)
  | wf_spec_env_record_get_binding_value : forall (L:env_loc) (x:prop_name) (b:bool),
      wf_ext_expr S str (spec_env_record_get_binding_value L x b)
  | wf_spec_env_record_get_binding_value_1 : forall (L:env_loc) (x:prop_name) (b:bool) (E:env_record),
      wf_env_record S str E ->
      wf_ext_expr S str (spec_env_record_get_binding_value_1 L x b E)
  | wf_spec_env_record_get_binding_value_2 : forall (x:prop_name) (b:bool) (l:object_loc) (o:out),
      wf_object_loc S str l ->
      wf_out S str o ->
      wf_ext_expr S str (spec_env_record_get_binding_value_2 x b l o)
  | wf_spec_env_record_create_immutable_binding : forall (L:env_loc) (x:prop_name),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_create_immutable_binding L x)
  | wf_spec_env_record_initialize_immutable_binding : forall (L:env_loc) (x:prop_name) (v:value),
      wf_env_loc S str L ->
      wf_value S str v ->
      wf_ext_expr S str (spec_env_record_initialize_immutable_binding L x v)
  | wf_spec_env_record_create_mutable_binding : forall (L:env_loc) (x:prop_name) (ob:option bool),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_create_mutable_binding L x ob)
  | wf_spec_env_record_create_mutable_binding_1 : forall (L:env_loc) (x:prop_name) (b:bool) (E:env_record),
      wf_env_loc S str L ->
      wf_env_record S str E ->
      wf_ext_expr S str (spec_env_record_create_mutable_binding_1 L x b E)
  | wf_spec_env_record_create_mutable_binding_2 : forall (L:env_loc) (x:prop_name) (b:bool) (l:object_loc) (o:out),
      wf_env_loc S str L ->
      wf_object_loc S str l ->
      wf_out S str o ->
      wf_ext_expr S str (spec_env_record_create_mutable_binding_2 L x b l o)
  | wf_spec_env_record_create_mutable_binding_3 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_env_record_create_mutable_binding_3 o)
  | wf_spec_env_record_set_mutable_binding : forall (L:env_loc) (x:prop_name) (v:value) (b:bool),
      wf_env_loc S str L ->
      wf_value S str v ->
      wf_ext_expr S str (spec_env_record_set_mutable_binding L x v b)
  | wf_spec_env_record_set_mutable_binding_1 : forall (L:env_loc) (x:prop_name) (v:value) (b:bool) (E:env_record),
      wf_env_loc S str L ->
      wf_value S str v ->
      wf_env_record S str E ->
      wf_ext_expr S str (spec_env_record_set_mutable_binding_1 L x v b E)
  | wf_spec_env_record_delete_binding : forall (L:env_loc) (x:prop_name),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_delete_binding L x)
  | wf_spec_env_record_delete_binding_1 : forall (L:env_loc) (x:prop_name) (E:env_record),
      wf_env_loc S str L ->
      wf_env_record S str E ->
      wf_ext_expr S str (spec_env_record_delete_binding_1 L x E)
  | wf_spec_env_record_create_set_mutable_binding : forall (L:env_loc) (x:prop_name) (ob:option bool) (v:value) (b:bool),
      wf_env_loc S str L ->
      wf_value S str v ->
      wf_ext_expr S str (spec_env_record_create_set_mutable_binding L x ob v b)
  | wf_spec_env_record_create_set_mutable_binding_1 : forall (o:out) (L:env_loc) (x:prop_name) (v:value) (b:bool),
      wf_out S str o ->
      wf_env_loc S str L ->
      wf_value S str v ->
      wf_ext_expr S str (spec_env_record_create_set_mutable_binding_1 o L x v b)

  (*spec_object_get*)
  | wf_spec_object_get : forall (v:value) (x:prop_name),
      wf_value S str v ->
      wf_ext_expr S str (spec_object_get v x)
  | wf_spec_object_get_1 : forall (v:value) (l:object_loc) (x:prop_name),
      wf_value S str v ->
      wf_object_loc S str l ->
      wf_ext_expr S str (spec_object_get_1 builtin_get_default v l x)
  | wf_spec_object_get_2 : forall (v:value) (S':state) (s:specret),
      wf_value S str v ->
      wf_specret S str s ->
      wf_ext_expr S str (spec_object_get_2 v s)

  (*spec_object_can_put*)
  | wf_spec_object_can_put : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_expr S str (spec_object_can_put l x)
  | wf_spec_object_can_put_1 : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_expr S str (spec_object_can_put_1 builtin_can_put_default l x)
  | wf_spec_object_can_put_2 : forall (l:object_loc) (x:prop_name) (sD:specret),
      wf_object_loc S str l ->
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_can_put_2 l x sD)
  | wf_spec_object_can_put_4 : forall (l:object_loc) (x:prop_name) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_expr S str (spec_object_can_put_4 l x v)
  | wf_spec_object_can_put_5 : forall (l:object_loc) (sD:specret),
      wf_object_loc S str l ->
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_can_put_5 l sD)
  | wf_spec_object_can_put_6 : forall (v:value) (b1 b2 b3 b':bool),
      wf_value S str v ->
      wf_ext_expr S str (spec_object_can_put_6 (attributes_data_intro v b1 b2 b3) b')

  (*spec_object_put*)
  | wf_spec_object_put : forall (x:prop_name) (v v':value) (b:bool),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_expr S str (spec_object_put v x v' b)
  | wf_spec_object_put_1 : forall (l:object_loc) (x:prop_name) (v v':value) (b:bool),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_expr S str (spec_object_put_1 builtin_put_default v l x v' b)
  | wf_spec_object_put_2 : forall (l:object_loc) (x:prop_name) (v v':value) (b:bool) (o:out),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_value S str v' ->
      wf_out S str o ->
      wf_ext_expr S str (spec_object_put_2 v l x v' b o)
  | wf_spec_object_put_3 : forall (l:object_loc) (x:prop_name) (v v':value) (b:bool) (sD:specret),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_value S str v' ->
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_put_3 v l x v' b sD)
  | wf_spec_object_put_4 : forall (l:object_loc) (x:prop_name) (v v':value) (b:bool) (sD:specret),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_value S str v' ->
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_put_4 v l x v' b sD)
  | wf_spec_object_put_5 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_object_put_5 o)
                  
  (*spec_object_has_prop*)
  | wf_spec_object_has_prop : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_expr S str (spec_object_has_prop l x)
  | wf_spec_object_has_prop_1 : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_expr S str (spec_object_has_prop_1 builtin_has_prop_default l x)
  | wf_spec_object_has_prop_2 : forall (sD:specret),
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_has_prop_2 sD)

  (*spec_object_define_own_prop*)
  | wf_spec_object_define_own_prop : forall (l:object_loc) (x:prop_name) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop l x Desc b)
  | wf_spec_object_define_own_prop_1 : forall (l:object_loc) (x:prop_name) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_1 builtin_define_own_prop_default l x Desc b)
  | wf_spec_object_define_own_prop_2 : forall (l:object_loc) (x:prop_name) (Desc:descriptor) (b:bool) (sD:specret),
      wf_object_loc S str l ->
      wf_descriptor S str Desc ->
      wf_specret S str sD ->
      wf_ext_expr S str (spec_object_define_own_prop_2 l x Desc b sD)
  | wf_spec_object_define_own_prop_3 : forall (l:object_loc) (x:prop_name) (Desc:descriptor) (b:bool) (D:full_descriptor) (b':bool),
      wf_object_loc S str l ->
      wf_descriptor S str Desc ->
      wf_full_descriptor S str D ->
      wf_ext_expr S str (spec_object_define_own_prop_3 l x Desc b D b')
  | wf_spec_object_define_own_prop_4 : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_4 l x A Desc b)
  | wf_spec_object_define_own_prop_5 : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_5 l x A Desc b)
(*  | wf_spec_object_define_own_prop_6a : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_6a l x A Desc b)*)
  | wf_spec_object_define_own_prop_6b : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_6b l x A Desc b)
  | wf_spec_object_define_own_prop_6c : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_6c l x A Desc b)
  | wf_spec_object_define_own_prop_reject : forall (b:bool),
      wf_ext_expr S str (spec_object_define_own_prop_reject b)
  | wf_spec_object_define_own_prop_write : forall (l:object_loc) (x:prop_name) (A:attributes) (Desc:descriptor) (b:bool),
      wf_object_loc S str l ->
      wf_attributes S str A ->
      wf_descriptor S str Desc ->
      wf_ext_expr S str (spec_object_define_own_prop_write l x A Desc b)
  | wf_spec_prim_value_get : forall (v:value) (x:prop_name),
      wf_value S str v ->
      wf_ext_expr S str (spec_prim_value_get v x)
  | wf_spec_prim_value_get_1 : forall (v:value) (x:prop_name) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (spec_prim_value_get_1 v x o)
  | wf_spec_prim_value_put : forall (v:value) (x:prop_name) (v':value) (b:bool),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_expr S str (spec_prim_value_put v x v' b)
  | wf_spec_prim_value_put_1 : forall (w:prim) (x:prop_name) (v:value) (b:bool) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (spec_prim_value_put_1 w x v b o)
  | wf_spec_returns : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (spec_returns o).




Inductive wf_ext_spec (S:state) (str:strictness_flag) : ext_spec -> Prop :=
  (*spec_to_int32*)
  | wf_spec_to_int32 : forall (v:value),
      wf_value S str v ->
      wf_ext_spec S str (spec_to_int32 v)
  | wf_spec_to_int32_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_to_int32_1 o)
  (*spec_to_uint_32*)
  | wf_spec_to_uint32 : forall (v:value),
      wf_value S str v ->
      wf_ext_spec S str (spec_to_uint32 v)
  | wf_spec_to_uint32_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_to_uint32_1 o)
  (*spec_convert_twice*)
  | wf_spec_convert_twice_to_primitive : forall (v v':value),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_spec S str (spec_convert_twice (spec_to_primitive_auto v) (spec_to_primitive_auto v'))
  | wf_spec_convert_twice_to_string : forall (v v':value),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_spec S str (spec_convert_twice (spec_to_string v) (spec_to_string v'))
  | wf_spec_convert_twice_to_number : forall (v v':value),
      wf_value S str v ->
      wf_value S str v' ->
      wf_ext_spec S str (spec_convert_twice (spec_to_number v) (spec_to_number v'))
  | wf_spec_convert_twice_1 : forall (S':state) (o:out) (ee:ext_expr),
      wf_out S str o ->
      state_of_out o S' ->
      wf_ext_expr S' str ee ->
      wf_ext_spec S str (spec_convert_twice_1 o ee)
  | wf_spec_convert_twice_2 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_spec S str (spec_convert_twice_2 v o)
  (*spec_expr_get_value_conv*)
  | wf_spec_expr_get_value_conv : forall (F:value -> ext_expr) (e:expr),
      (forall (v:value) (S':state), wf_state S' -> wf_value S' str v -> wf_ext_expr S' str (F v)) ->
      wf_expr S str e ->
      wf_ext_spec S str (spec_expr_get_value_conv F e)
  | wf_spec_expr_get_value_conv_1 : forall (F:value -> ext_expr) (s:specret),
      (forall (v:value) (S':state), wf_state S' -> wf_value S' str v -> wf_ext_expr S' str (F v)) ->
      wf_specret S str s ->
      wf_ext_spec S str (spec_expr_get_value_conv_1 F s)
  | wf_spec_expr_get_value_conv_2 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_expr_get_value_conv_2 o)
  (*spec_object_get_own_prop*)
  | wf_spec_object_get_own_prop : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_spec S str (spec_object_get_own_prop l x)
  | wf_spec_object_get_own_prop_1 : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_spec S str (spec_object_get_own_prop_1 builtin_get_own_prop_default l x)
  | wf_spec_object_get_own_prop_2 : forall (l:object_loc) (x:prop_name) (oA:option attributes),
      wf_object_loc S str l ->
      wf_oattributes S str oA ->
      wf_ext_spec S str (spec_object_get_own_prop_2 l x oA)
  (*spec_ref_get_value*)
  | wf_spec_get_value : forall (rv:resvalue),
      wf_resvalue S str rv ->
      wf_ext_spec S str (spec_get_value rv)
  | wf_spec_get_value_ref_b_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_get_value_ref_b_1 o)
  | wf_spec_get_value_ref_c_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_get_value_ref_c_1 o)
  (*spec_expr_get_value*)
  | wf_spec_expr_get_value : forall (e:expr),
      wf_expr S str e ->
      wf_ext_spec S str (spec_expr_get_value e)
  | wf_spec_expr_get_value_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_expr_get_value_1 o)
  (*spec_lexical_env_get_identifier_ref*)
  | wf_spec_lexical_env_get_identifier_ref : forall (lex:lexical_env) (x:prop_name) (str':bool),
      wf_lexical_env S str lex ->
      wf_ext_spec S str (spec_lexical_env_get_identifier_ref lex x str')
  | wf_spec_lexical_env_get_identifier_ref_1 : forall (L:env_loc) (lex:lexical_env) (x:prop_name) (str':bool),
      wf_env_loc S str L ->
      wf_lexical_env S str lex ->
      wf_ext_spec S str (spec_lexical_env_get_identifier_ref_1 L lex x str')
  | wf_spec_lexical_env_get_identifier_ref_2 : forall (L:env_loc) (lex:lexical_env) (x:prop_name) (str':bool) (o:out),
      wf_env_loc S str L ->
      wf_lexical_env S str lex ->
      wf_out S str o ->
      wf_ext_spec S str (spec_lexical_env_get_identifier_ref_2 L lex x str' o)
  (*spec_error_spec*)
  | wf_spec_error_spec : forall (ne:native_error),
      wf_ext_spec S str (spec_error_spec ne)
  | wf_spec_error_spec_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_error_spec_1 o)
  (*spec_object_get_prop*)
  | wf_spec_object_get_prop : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_spec S str (spec_object_get_prop l x)
  | wf_spec_object_get_prop_1 : forall (l:object_loc) (x:prop_name),
      wf_object_loc S str l ->
      wf_ext_spec S str (spec_object_get_prop_1 builtin_get_prop_default l x)
  | wf_spec_object_get_prop_2 : forall (l:object_loc) (x:prop_name) (sD:specret),
      wf_object_loc S str l ->
      wf_specret S str sD ->
      wf_ext_spec S str (spec_object_get_prop_2 l x sD)
  | wf_spec_object_get_prop_3 : forall (l:object_loc) (x:prop_name) (v:value),
      wf_object_loc S str l ->
      wf_value S str v ->
      wf_ext_spec S str (spec_object_get_prop_3 l x v).
