

~ 700 reduction rules (~ 3000 non empty lines)
~ 450 intermediate forms
~ 3000 lines of correctness proofs jsref/jscert
~ 2500 lines of interpreter code (~ 2000 non empty lines)
~ ? lines of definitions in Syntax 
~ ? lines of definitions in Preliminary 
~ ? lines of proofs (SyntaxAux, PreliminaryAux, IntermAux)

~ 3300 lines of correctness proofs jsref/jscert


============================================================================


Daniele: hide commented stuff in JsPreliminary.

2) whoever is working on the code for "switch", what's the status?
6) we'll need a regexp to remove all LATER and TODO for the release
7) For Alan: handle all the TODOs in the files (except Shared & Correctness).

====================
Waiting for fixes:


====================

Arthur:

run_binary_op_correct
run red_expr_delete
run_elements preuve

====================

Martin:

--switch--> proof


============================================================================


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


=== semi-libraries ===

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



