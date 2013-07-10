

====================
=== CHECK:

red_spec_object_define_own_prop_5_generic 
  => the negation of the condition does not appear in the others; is it correct?


==> get rid of the events in pretty rules (with a flag)


====================

Arthur:

red_spec_object_put_3_not_data 
red_spec_object_put_4_accessor 
red_spec_object_put_4_not_accessor_object 
red_spec_object_put_4_not_accessor_prim 

red_spec_object_get_1_function 
red_spec_function_get_1_error 
red_spec_function_get_1_normal 
red_spec_object_has_instance 
red_spec_object_has_instance_1_prim 
red_spec_object_has_instance_1_object 
red_spec_function_has_instance_1_prim 
red_spec_function_has_instance_1_object 


red_spec_creating_function_object_proto 
red_spec_creating_function_object_proto_1 
red_spec_creating_function_object_proto_2 
red_spec_creating_function_object 
red_spec_creating_function_object_1 
red_spec_creating_function_object_2_not_strict 
red_spec_creating_function_object_2_strict 
red_spec_creating_function_object_3 
red_spec_creating_function_object_4 

red_spec_to_descriptor_not_object 
red_spec_to_descriptor_object 
red_spec_to_descriptor_1a 
red_spec_to_descriptor_1b_false 
red_spec_to_descriptor_1b_true 
red_spec_to_descriptor_1c 
red_spec_to_descriptor_2a 
red_spec_to_descriptor_2b_false 
red_spec_to_descriptor_2b_true 
red_spec_to_descriptor_2c 
red_spec_to_descriptor_3a 
red_spec_to_descriptor_3b_false 
red_spec_to_descriptor_3b_true 
red_spec_to_descriptor_3c 
red_spec_to_descriptor_4a 
red_spec_to_descriptor_4b_false 
red_spec_to_descriptor_4b_true 
red_spec_to_descriptor_4c 
red_spec_to_descriptor_5a 
red_spec_to_descriptor_5b_false 
red_spec_to_descriptor_5b_true 
red_spec_to_descriptor_5c_error 
red_spec_to_descriptor_5c_ok 
red_spec_to_descriptor_6a 
red_spec_to_descriptor_6b_false 
red_spec_to_descriptor_6b_true 
red_spec_to_descriptor_6c_error 
red_spec_to_descriptor_6c_ok 
red_spec_to_descriptor_7_error 
red_spec_to_descriptor_7_ok 

red_spec_create_new_function_in 

red_javascript_intro 
(* Need a more precise lemma for [spec_binding_inst], and I need that someone reread the comments I've put in the rule [red_javascript_intro]. *)

red_spec_convert_twice 
red_spec_convert_twice_1 
red_spec_convert_twice_2 
red_spec_to_int32 
red_spec_to_int32_1 
red_spec_to_uint32 
red_spec_to_uint32_1 

switch
do_while
binary ops

====================

Martin:

new program for prog_block

new program for do_while


Implementing the new stat_block, and code do_while, following while.

Merging if_success* (in a branch)


red_spec_call 
red_spec_constructor 
red_spec_call_1_prealloc 
red_spec_construct_1_prealloc 

red_expr_call 
red_expr_call_1 
red_expr_call_2 
red_expr_call_3 
red_expr_call_3_callable 
red_expr_call_4_prop 
red_expr_call_4_env 
red_expr_call_4_not_ref 
red_expr_call_5_eval 
red_expr_call_5_not_eval 

red_spec_call_1_default 
red_spec_call_default 
red_spec_call_default_1 
red_spec_call_default_2_body 
red_spec_call_default_2_empty_body 
red_spec_call_default_3_return 
red_spec_call_default_3_normal 
red_spec_construct_1_default 
red_spec_construct_default 
red_spec_construct_default_1 
red_spec_function_construct_2 

red_spec_call_object_call 
red_spec_call_object_call_1_null_or_undef 
red_spec_call_object_call_1_other 
red_spec_call_object_new 
red_spec_call_object_new_1_object 
red_spec_call_object_new_1_prim 
red_spec_call_object_new_1_null_or_undef 

red_spec_call_throw_type_error 
red_spec_call_global_eval 
red_spec_call_global_eval_1_not_string 
red_spec_call_global_eval_1_string_not_parse 
red_spec_call_global_eval_1_string_parse 
red_spec_call_global_eval_2 
red_spec_call_global_eval_3_normal_value 
red_spec_call_global_eval_3_normal_empty 
red_spec_call_global_eval_3_throw 

red_spec_entering_eval_code 
red_spec_entering_eval_code_1 
red_spec_entering_eval_code_2 
red_spec_entering_func_code 
red_spec_entering_func_code_1_strict 
red_spec_entering_func_code_1_null_or_undef 
red_spec_entering_func_code_1_not_object 
red_spec_entering_func_code_2 
red_spec_entering_func_code_1_object 
red_spec_entering_func_code_3 
red_spec_entering_func_code_4 

red_spec_binding_inst_formal_params_empty 
red_spec_binding_inst_formal_params_non_empty 
red_spec_binding_inst_formal_params_1_not_declared 
red_spec_binding_inst_formal_params_2 
red_spec_binding_inst_formal_params_1_declared 
red_spec_binding_inst_formal_params_3 
red_spec_binding_inst_formal_params_4 
red_spec_binding_inst_function_decls_nil 
red_spec_binding_inst_function_decls_cons 
red_spec_binding_inst_function_decls_1 
red_spec_binding_inst_function_decls_2_false 
red_spec_binding_inst_function_decls_2_true_global 
red_spec_binding_inst_function_decls_3_true 
red_spec_binding_inst_function_decls_4 
red_spec_binding_inst_function_decls_3_false_type_error 
red_spec_binding_inst_function_decls_3_false 
red_spec_binding_inst_function_decls_2_true 
red_spec_binding_inst_function_decls_5 
red_spec_binding_inst_function_decls_6 
red_spec_binding_inst_arg_obj 
red_spec_binding_inst_arg_obj_1_strict 
red_spec_binding_inst_arg_obj_2 
red_spec_binding_inst_arg_obj_1_not_strict 
red_spec_binding_inst_var_decls_nil 
red_spec_binding_inst_var_decls_cons 
red_spec_binding_inst_var_decls_1_true 
red_spec_binding_inst_var_decls_1_false 
red_spec_binding_inst_var_decls_2 
red_spec_binding_inst 
red_spec_binding_inst_1_function 
red_spec_binding_inst_2 
red_spec_binding_inst_1_not_function 
red_spec_binding_inst_3 
red_spec_binding_inst_4 
red_spec_binding_inst_5 
red_spec_binding_inst_6_arguments 
red_spec_binding_inst_7 
red_spec_binding_inst_6_no_arguments 
red_spec_binding_inst_8 



=== can be skipped ===

red_spec_object_get_own_prop_args_obj 
red_spec_object_get_own_prop_args_obj_1_undef 
red_spec_object_get_own_prop_args_obj_1_attrs 
red_spec_object_get_own_prop_args_obj_2_attrs 
red_spec_object_get_own_prop_args_obj_3 
red_spec_object_get_own_prop_args_obj_2_undef 
red_spec_object_get_own_prop_args_obj_4 

red_spec_arguments_object_map 
red_spec_arguments_object_map_1 
red_spec_arguments_object_map_2_nil 
red_spec_arguments_object_map_2_cons 
red_spec_arguments_object_map_3_skip 
red_spec_arguments_object_map_3_cont_skip 
red_spec_arguments_object_map_3_cont_cont 
red_spec_arguments_object_map_4 
red_spec_arguments_object_map_5 
red_spec_arguments_object_map_6 
red_spec_arguments_object_map_7 
red_spec_arguments_object_map_8_cons 
red_spec_arguments_object_map_8_nil 
red_spec_create_arguments_object 
red_spec_create_arguments_object_1 
red_spec_create_arguments_object_2_non_strict 
red_spec_create_arguments_object_2_strict 
red_spec_create_arguments_object_3 
red_spec_create_arguments_object_4

red_spec_object_define_own_prop_args_obj 
red_spec_object_define_own_prop_args_obj_1 
red_spec_object_define_own_prop_args_obj_2_false 
red_spec_object_define_own_prop_args_obj_2_true_acc 
red_spec_object_define_own_prop_args_obj_2_true_not_acc_some 
red_spec_object_define_own_prop_args_obj_3 
red_spec_object_define_own_prop_args_obj_2_true_not_acc_none 
red_spec_object_define_own_prop_args_obj_4_false 
red_spec_object_define_own_prop_args_obj_5 
red_spec_object_define_own_prop_args_obj_4_not_false 
red_spec_object_define_own_prop_args_obj_2_true_undef 
red_spec_object_define_own_prop_args_obj_6 

red_spec_make_arg_getter 
red_spec_make_arg_setter 

red_spec_object_get_args_obj 
red_spec_object_get_args_obj_1_undef 
red_spec_object_get_args_obj_1_attrs 
red_spec_object_delete_args_obj 
red_spec_object_delete_args_obj_1 
red_spec_object_delete_args_obj_2_if 
red_spec_object_delete_args_obj_3 
red_spec_object_delete_args_obj_2_else 
red_spec_object_delete_args_obj_4 









==============================================

*) Say that we formalize all of the core language (out of libraries).
   About JS-specific functions from library: 
   work in progress (almost all specified, no jscert-to-jsref proof yet)

*) Section 4:
-- count the number pages of ES5 that we actually cover

*) Section 6:
Section 6 needs to be filled (without using too much space)
-- section 6.1: not sure it brings new information compared with what's been said before

*) Section 5: 
-- Figure 7 contains "Fixpoint build_runs max_step" which is redundant with the previous def
-- Figure 4 needs to inline the definition of "vret", which is not defined
-- There is undefined reference to "abort"; 
-- An example what how the abort rule propagates exceptions (we don't have to show the generic abort rule though, we can just say that all abort rules are actually factorized as one, see pretty-big-step paper for details).

*) running spellchecker on paper

*) try to see if \paragraph would look nicer than \stitle

*) to release Coq scripts, we'll need a script for hiding LATER and TODO (using a regexp)
