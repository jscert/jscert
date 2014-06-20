Set Implicit Arguments.
Require Export JsPrettyInterm.

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


(*well-formedness for programs*)
(*the state and the strictness flag are currently unused but may be needed later*)

Inductive wf_expr (S:state) (str:strictness_flag) : expr -> Prop :=
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
      wf_expr S str (expr_binary_op e1 op e2)
  | wf_expr_conditional : forall (e1 e2 e3 : expr),
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_expr S str e3 ->
      wf_expr S str (expr_conditional e1 e2 e3)
  | wf_expr_assign : forall (e1 e2:expr) (opo:option binary_op),
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_expr S str (expr_assign e1 opo e2).


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
  | wf_stat_var_decl : forall (l:list (string*option expr)),
      Forall (wf_var_decl S str) l ->
      wf_stat S str (stat_var_decl l).


Inductive wf_element (S:state) (str:strictness_flag) : element -> Prop :=
  | wf_element_stat : forall (t:stat),
      wf_stat S str t ->
      wf_element S str (element_stat t).


Inductive wf_prog (S:state) (str:strictness_flag): prog -> Prop :=
  | wf_prog_intro : forall (l:list element),
      Forall (wf_element S str) l ->
      wf_prog S str (prog_intro str l).




(*well-formedness for states*)

Definition wf_state (S:state) :=
  Heap.indom (state_object_heap S) (object_loc_prealloc prealloc_global)
  /\ Heap.indom (state_env_record_heap S) env_loc_global_env_record.




(*well-formedness for execution contexts (scope chains)*)

Definition only_global_scope (C:execution_ctx) :=
  execution_ctx_lexical_env C = (env_loc_global_env_record::nil). (*maybe too strict*)


Definition wf_execution_ctx (str:strictness_flag) (C:execution_ctx) :=
  only_global_scope C.




(*well-formedness for out*)

(*check that the env_loc is bound to some env_record in the state*)
Inductive wf_env_loc (S:state) (str:strictness_flag) : env_loc -> Prop :=
  | wf_env_loc_bound : forall (L:env_loc),
      (*env_record_binds S L E ->  ie Heap.binds (state_env_record_heap S) L E, JsPreliminary.v l830*)
      Heap.indom (state_env_record_heap S) L ->
      wf_env_loc S str L.


Inductive wf_value (S:state) (str:strictness_flag) : value -> Prop :=
  | wf_value_prim : forall w:prim,
      wf_value S str (value_prim w).


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


Inductive wf_res (S:state) (str:strictness_flag) : res -> Prop :=
  | wf_res_intro : forall (rv:resvalue) (lab:label), (*not sure about the label and the type*)
      wf_resvalue S str rv ->
      wf_res S str (res_intro restype_normal rv lab).


Inductive wf_out (S:state) (str:strictness_flag) : out -> Prop :=
(*  | wf_out_div : wf_out S str out_div*) (*shouldn't happen actually*)
  | wf_out_ter : forall (S':state) (R:res),
      wf_state S' ->
      state_extends S' S ->
      wf_res S' str R ->
      wf_out S str (out_ter S' R).


Inductive wf_attributes (S:state) (str:strictness_flag) : attributes -> Prop :=
  | wf_attributes_data_of : forall (v:value) (b1 b2 b3:bool),
      wf_value S str v ->
      wf_attributes S str (attributes_data_of (attributes_data_intro v b1 b2 b3))
  | wf_attributes_accessor_of : forall (v v':value) (b b':bool),
      wf_value S str v ->
      wf_value S str v' ->
      wf_attributes S str (attributes_accessor_of (attributes_accessor_intro v v' b b)).


Inductive wf_full_descriptor (S:state) (str:strictness_flag) : full_descriptor -> Prop :=
  | wf_full_descriptor_undef : wf_full_descriptor S str full_descriptor_undef
  | wf_full_descriptor_some : forall (A:attributes),
      wf_attributes S str A ->
      wf_full_descriptor S str (full_descriptor_some A).

(*well-formedness for intermediate forms*)
Inductive wf_specret_value : state -> strictness_flag -> specret value -> Prop :=
  | wf_specret_value_out : forall (S:state) (str:strictness_flag) (o:out),
      wf_out S str o ->
      wf_specret_value S str (@specret_out value o)
  | wf_specret_value_val : forall (str:strictness_flag) (t:value) (S S':state),
      wf_state S' ->
      wf_value S' str t ->
      state_extends S' S ->
      wf_specret_value S str (@specret_val value S' t).

Inductive wf_specret_int : state -> strictness_flag -> specret int -> Prop :=
  | wf_specret_int_out : forall (S:state) (str:strictness_flag) (o:out),
      wf_out S str o ->
      wf_specret_int S str (@specret_out int o)
  | wf_specret_int_val : forall (S S':state) (str:strictness_flag) (t:int),
      wf_state S' ->
      state_extends S' S ->
      wf_specret_int S str (@specret_val int S' t).

Inductive wf_specret_valuevalue : state -> strictness_flag -> specret (value*value) -> Prop :=
  | wf_specret_valuevalue_out : forall (S:state) (str:strictness_flag) (o:out),
      wf_out S str o ->
      wf_specret_valuevalue S str (@specret_out (value*value) o)
  | wf_specret_valuevalue_val : forall (S S':state) (str:strictness_flag) (v1 v2:value),
      wf_state S' ->
      wf_value S' str v1 ->
      wf_value S' str v2 ->
      state_extends S' S ->
      wf_specret_valuevalue S str (@specret_val (value*value) S' (v1,v2)).

Inductive wf_specret_ref : state -> strictness_flag -> specret ref -> Prop :=
  | wf_specret_ref_out : forall (S:state) (str:strictness_flag) (o:out),
      wf_out S str o ->
      wf_specret_ref S str (@specret_out ref o)
  | wf_specret_ref_val : forall (S S':state) (str:strictness_flag) (r:ref),
      wf_state S' ->
      wf_ref S' str r ->
      state_extends S' S ->
      wf_specret_ref S str (@specret_val ref S' r).

        
Inductive wf_specret_full_descriptor : state -> strictness_flag -> specret full_descriptor -> Prop :=
  | wf_specret_full_descriptor_out : forall (S:state) (str:strictness_flag) (o:out),
      wf_out S str o ->
      wf_specret_full_descriptor S str (@specret_out full_descriptor o)
  | wf_specret_full_descriptor_val : forall (S S':state) (str:strictness_flag) (D:full_descriptor),
      wf_state S' ->
      wf_full_descriptor S' str D ->
      state_extends S' S ->
      wf_specret_full_descriptor S str (@specret_val full_descriptor S' D).



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
  | wf_stat_basic : forall (t:stat),
      wf_stat S str t ->
      wf_ext_stat S str (stat_basic t)
  | wf_stat_expr_1 : forall (sv:specret value),
      wf_specret_value S str sv ->
      wf_ext_stat S str (stat_expr_1 sv)
  | wf_stat_var_decl_1 : forall (S':state) (o:out) (l:list (string*option expr)),
      wf_out S str o ->
      state_of_out o S' ->
      Forall (wf_var_decl S' str) l ->
      wf_ext_stat S str (stat_var_decl_1 o l)
  | wf_stat_var_decl_item : forall (d:string*option expr),
      wf_var_decl S str d ->
      wf_ext_stat S str (stat_var_decl_item d)
  | wf_stat_var_decl_item_1 : forall (s:string) (sr:specret ref) (e:expr),
      wf_specret_ref S str sr ->
      wf_expr S str e ->
      wf_ext_stat S str (stat_var_decl_item_1 s sr e)
  | wf_stat_var_decl_item_2 : forall (s:string) (r:ref) (sv:specret value),
      wf_ref S str r ->
      wf_specret_value S str sv ->
      wf_ext_stat S str (stat_var_decl_item_2 s r sv)
  | wf_stat_var_decl_item_3 : forall (s:string) (o:out),
      wf_out S str o ->
      wf_ext_stat S str (stat_var_decl_item_3 s o).




Inductive wf_ext_expr (S:state) (str:strictness_flag) : ext_expr -> Prop :=
  | wf_expr_basic : forall e:expr,
      wf_expr S str e ->
      wf_ext_expr S str (expr_basic e)
  | wf_expr_identifier_1 : forall sr:specret ref,
      wf_specret_ref S str sr ->
      wf_ext_expr S str (expr_identifier_1 sr)
  | wf_expr_unary_op_1 : forall (op:unary_op) (sv:specret value),
      wf_specret_value S str sv ->
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
  | wf_expr_typeof_2 : forall (sv:specret value),
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_typeof_2 sv)
  | wf_expr_prepost_1 : forall (op:unary_op) (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_prepost_1 op o)
  | wf_expr_prepost_2 : forall (op:unary_op) (R:res) (sv:specret value),
      wf_res S str R ->
      wf_specret_value S str sv ->
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
  | wf_expr_unary_op_bitwise_not_1 : forall (si:specret int),
      wf_specret_int S str si ->
      wf_ext_expr S str (expr_unary_op_bitwise_not_1 si)
  | wf_expr_unary_op_not_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_expr S str (expr_unary_op_not_1 o)
  | wf_expr_conditional_1 : forall (sv:specret value) (e1 e2:expr),
      wf_specret_value S str sv ->
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_ext_expr S str (expr_conditional_1 sv e1 e2)
  | wf_expr_conditional_1': forall (o:out) (e1 e2:expr),
      wf_out S str o ->
      wf_expr S str e1 ->
      wf_expr S str e2 ->
      wf_ext_expr S str (expr_conditional_1' o e1 e2)
  | wf_expr_conditional_2 : forall (sv:specret value),
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_conditional_2 sv)
  | wf_expr_binary_op_1 : forall (op:binary_op) (sv:specret value) (e:expr),
      wf_specret_value S str sv ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_binary_op_1 op sv e)
  | wf_expr_binary_op_2 : forall (op:binary_op) (v:value) (sv:specret value),
      wf_value S str v ->
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_binary_op_2 op v sv)
  | wf_expr_binary_op_3 : forall (op:binary_op) (v1:value) (v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (expr_binary_op_3 op v1 v2)
  | wf_expr_binary_op_add_1 : forall (svv:specret (value*value)),
      wf_specret_valuevalue S str svv ->
      wf_ext_expr S str (expr_binary_op_add_1 svv)
  | wf_expr_binary_op_add_string_1 : forall (svv:specret (value*value)),
      wf_specret_valuevalue S str svv ->
      wf_ext_expr S str (expr_binary_op_add_string_1 svv)
  | wf_expr_puremath_op_1 : forall (f:(number -> number -> number)) (svv:specret (value*value)),
      wf_specret_valuevalue S str svv ->
      wf_ext_expr S str (expr_puremath_op_1 f svv)
  | wf_expr_shift_op_1 : forall (f:int -> int -> int) (si:specret int) (v:value),
      wf_specret_int S str si ->
      wf_value S str v ->
      wf_ext_expr S str (expr_shift_op_1 f si v)
  | wf_expr_shift_op_2 : forall (f:int -> int -> int) (k:int) (si:specret int),
      wf_specret_int S str si ->
      wf_ext_expr S str (expr_shift_op_2 f k si)
  | wf_expr_inequality_op_1 : forall (b1 b2:bool) (v1 v2:value),
      wf_value S str v1 ->
      wf_value S str v2 ->
      wf_ext_expr S str (expr_inequality_op_1 b1 b2 v1 v2)
  | wf_expr_inequality_op_2 : forall (b1 b2:bool) (svv:specret (value*value)),
      wf_specret_valuevalue S str svv ->
      wf_ext_expr S str (expr_inequality_op_2 b1 b2 svv)
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
      wf_ext_expr S str (spec_equal_3 v1 f v2)
  | wf_spec_equal_4 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (spec_equal_4 v o)
  | wf_expr_bitwise_op_1 : forall (f:int -> int -> int) (si:specret int) (v:value),
      wf_specret_int S str si ->
      wf_value S str v ->
      wf_ext_expr S str (expr_bitwise_op_1 f si v)
  | wf_expr_bitwise_op_2 : forall (f:int -> int -> int) (k:int) (si:specret int),
      wf_specret_int S str si ->
      wf_ext_expr S str (expr_bitwise_op_2 f k si)
  | wf_expr_lazy_op_1 : forall (b:bool) (sv:specret value) (e:expr),
      wf_specret_value S str sv ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_lazy_op_1 b sv e)
  | wf_expr_lazy_op_2 : forall (b:bool) (v:value) (o:out) (e:expr),
      wf_value S str v ->
      wf_out S str o ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_lazy_op_2 b v o e)
  | wf_expr_lazy_op_2_1 : forall (sv:specret value),
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_lazy_op_2_1 sv)
  | wf_expr_assign_1 : forall (o:out) (oop:option binary_op) (e:expr),
      wf_out S str o ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_assign_1 o oop e)
  | wf_expr_assign_2 : forall (R:res) (sv:specret value) (op:binary_op) (e:expr),
      wf_res S str R ->
      wf_specret_value S str sv ->
      wf_expr S str e ->
      wf_ext_expr S str (expr_assign_2 R sv op e)
  | wf_expr_assign_3 : forall (R:res) (v:value) (op:binary_op) (sv:specret value),
      wf_res S str R ->
      wf_value S str v ->
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_assign_3 R v op sv)
  | wf_expr_assign_3' : forall (R:res) (o:out),
      wf_res S str R ->
      wf_out S str o ->
      wf_ext_expr S str (expr_assign_3' R o)
  | wf_expr_assign_4 : forall (R:res) (sv:specret value),
      wf_res S str R ->
      wf_specret_value S str sv ->
      wf_ext_expr S str (expr_assign_4 R sv)
  | wf_expr_assign_5 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_expr S str (expr_assign_5 v o)
  | wf_spec_binding_inst : forall (p:prog), (*probably too strict, but I needed this*)
      wf_prog S str p ->
      wf_ext_expr S str (spec_binding_inst codetype_global None p nil)
  | wf_spec_error : forall (n:native_error),
      wf_ext_expr S str (spec_error n)
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
  | wf_spec_object_delete_2 : forall (l:object_loc) (x:prop_name) (b:bool) (sD:(specret full_descriptor)),
      wf_specret_full_descriptor S str sD ->
      wf_ext_expr S str (spec_object_delete_2 l x b sD)
  | wf_spec_object_delete_3 : forall (l:object_loc) (x:prop_name) (b:bool) (b':bool),
      wf_ext_expr S str (spec_object_delete_3 l x b b')
  | wf_spec_env_record_has_binding : forall (L:env_loc) (x:prop_name),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_has_binding L x)
  | wf_spec_env_record_has_binding_1 : forall (L:env_loc) (x:prop_name) (E:env_record),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_has_binding_1 L x E)
  | wf_spec_env_record_get_binding_value : forall (L:env_loc) (x:prop_name) (b:bool),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_get_binding_value L x b)
  | wf_spec_env_record_get_binding_value_1 : forall (L:env_loc) (x:prop_name) (b:bool) (E:env_record),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_get_binding_value_1 L x b E)
  | wf_spec_env_record_get_binding_value_2 : forall (x:prop_name) (b:bool) (l:object_loc) (o:out),
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
      wf_ext_expr S str (spec_env_record_create_mutable_binding_1 L x b E)
  | wf_spec_env_record_create_mutable_binding_2 : forall (L:env_loc) (x:prop_name) (b:bool) (l:object_loc) (o:out),
      wf_env_loc S str L ->
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
      wf_ext_expr S str (spec_env_record_set_mutable_binding_1 L x v b E)
  | wf_spec_env_record_delete_binding : forall (L:env_loc) (x:prop_name),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_delete_binding L x)
  | wf_spec_env_record_delete_binding_1 : forall (L:env_loc) (x:prop_name) (E:env_record),
      wf_env_loc S str L ->
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
  | wf_spec_env_record_implicit_this_value : forall (L:env_loc),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_implicit_this_value L)
  | wf_spec_env_record_implicit_this_value_1 : forall (L:env_loc) (E:env_record),
      wf_env_loc S str L ->
      wf_ext_expr S str (spec_env_record_implicit_this_value_1 L E).




(*may need these ones too*)
(*(** Extended expressions for comparison *)

  | spec_eq : value -> value -> ext_expr
  | spec_eq0 : value -> value -> ext_expr
  | spec_eq1 : value -> value -> ext_expr
  | spec_eq2 : ext_expr -> value -> value -> ext_expr
  | spec_prim_value_get : value -> prop_name -> ext_expr
  | spec_prim_value_get_1 : value -> prop_name -> out -> ext_expr
  | spec_prim_value_put : value -> prop_name -> value -> bool -> ext_expr
  | spec_prim_value_put_1 : prim -> prop_name -> value -> bool -> out -> ext_expr

  

*)


(*may also need things from ext_spec*)


Inductive wf_ext_spec (S:state) (str:strictness_flag) : ext_spec -> Prop :=
  | wf_spec_identifier_resolution : forall (C:execution_ctx) (x:prop_name),
      wf_execution_ctx str C ->
      wf_ext_spec S str (spec_identifier_resolution C x)
  | wf_spec_expr_get_value : forall (e:expr),
      wf_expr S str e ->
      wf_ext_spec S str (spec_expr_get_value e)
  | wf_spec_get_value : forall (rv:resvalue),
      wf_resvalue S str rv ->
      wf_ext_spec S str (spec_get_value rv)
  | wf_spec_to_int32 : forall (v:value),
      wf_value S str v ->
      wf_ext_spec S str (spec_to_int32 v)
  | wf_spec_to_int32_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_to_int32_1 o)
  | wf_spec_to_uint32 : forall (v:value),
      wf_value S str v ->
      wf_ext_spec S str (spec_to_uint32 v)
  | wf_spec_to_uint32_1 : forall (o:out),
      wf_out S str o ->
      wf_ext_spec S str (spec_to_uint32_1 o)
  | wf_spec_convert_twice : forall (ee:ext_expr) (ee':ext_expr),
      wf_ext_expr S str ee ->
      wf_ext_expr S str ee' ->
      wf_ext_spec S str (spec_convert_twice ee ee')
  | wf_spec_convert_twice_1 : forall (o:out) (ee:ext_expr),
      wf_out S str o ->
      wf_ext_expr S str ee ->
      wf_ext_spec S str (spec_convert_twice_1 o ee)
  | wf_spec_convert_twice_2 : forall (v:value) (o:out),
      wf_value S str v ->
      wf_out S str o ->
      wf_ext_spec S str (spec_convert_twice_2 v o).
                                                        