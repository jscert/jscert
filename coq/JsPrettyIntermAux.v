Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux JsPreliminary JsPrettyInterm.

(**************************************************************)
(** ** Implicit Types *)

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
Implicit Type E : env_record. (* suggested R *)
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
(** ** Extracting outcome from an extended expression. *)

(** The [out_of_ext_*] family of definitions is used by
    the generic abort rule, which propagates exceptions,
    and divergence, break and continues. *)

Definition out_of_ext_expr (e : ext_expr) : option out :=
  match e with
  (* TODO: update later
  | expr_basic _ => None
  | expr_list_then _ _ => None
  | expr_list_then_1 _ _ _ => None
  | expr_list_then_2 _ _ o _ => Some o
  | expr_object_1 _ _ _ => None
  | expr_access_1 o _ => Some o
  | expr_access_2 _ o => Some o
  | expr_new_1 o _ => Some o
  | expr_new_2 _ _ _ => None
  | expr_new_3 _ o => Some o
  | expr_call_1 o _ => Some o
  | expr_call_2 _ _ _ => None
  | expr_call_3 _ _ _ => None
  | expr_call_4 o => Some o
  | expr_unary_op_1 _ o => Some o
  | expr_unary_op_2 _ _ => None
  | expr_binary_op_1 o _ _ => Some o
  | expr_binary_op_2 _ _ _ _ => None
     (* TODO (Arthur does not understand this comment:
        If the `option out' is not `None' then the `out' is returned anyway,
        independently of wheither it aborts or not. *)
  | expr_binary_op_3 _ _ _ => None
  | expr_binary_op_add_1 _ _ => None
  | expr_assign_1 o _ _ => Some o
  | expr_assign_2 _ o => Some o
  | expr_assign_2_op _ _ _ o => Some o
  | spec_to_number_1 o => Some o
  | spec_to_integer_1 o => Some o
  | spec_to_string_1 o => Some o
  | spec_to_default_1 _ _ _ => None
  | spec_to_default_2 _ _ => None
  | spec_to_default_3 => None
  | spec_to_default_sub_1 _ _ _ => None
  | spec_to_default_sub_2 _ _ _ => None
  | spec_convert_twice _ _ _ => None
  | spec_convert_twice_1 o _ _ => Some o
  | spec_convert_twice_2 o _ => Some o
  (* TODO: missing new extended forms here *)
  *)
  | _ => None
  (* TODO: remove the line above to ensure that nothing forgotten *)
  end.

Definition out_of_ext_stat (p : ext_stat) : option out :=
  match p with
  (* TODO: update later
  | stat_basic _ => None
  | stat_seq_1 o _ => Some o
  | stat_var_decl_1 o => Some o
  | stat_if_1 o _ _ => Some o
  | stat_if_2 o _ _ => out_some_out o
  | stat_if_3 o _ _ => out_some_out o
  | stat_while_1 _ o _ => Some o
  | stat_while_2 _ _ _ => None
  | stat_while_3 _ _ o => Some o
  | stat_throw_1 o => Some o
  | stat_try_1 o _ _=> Some o
  | stat_try_2 _ _ _ => None
  | stat_try_3 o _ => Some o
  | stat_try_4 _ o => Some o
  | stat_with_1 o _ => Some o
  *)
  | _ => None
  end.

Definition out_of_ext_prog (p : ext_prog) : option out :=
  match p with
  | prog_basic _ => None
  | prog_seq_1 o _ => Some o
  end.

