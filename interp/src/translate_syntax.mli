
exception CoqSyntaxDoesNotSupport of string
exception Empty_list

val string_to_coq : string -> char list

val unary_op_to_coq : Parser_syntax.unary_op -> Interpreter.unary_op
val arith_op_to_coq : Parser_syntax.arith_op -> Interpreter.binary_op
val bin_op_to_coq : Parser_syntax.bin_op -> Interpreter.binary_op

val exp_to_literal : Parser_syntax.exp -> Interpreter.literal

val exp_to_exp : Parser_syntax.exp -> Interpreter.expr
val exp_to_stat : Parser_syntax.exp -> Interpreter.stat
val exp_to_prog : Parser_syntax.exp -> Interpreter.prog
val exp_to_elem : Parser_syntax.exp -> Interpreter.element
val exp_to_funcbody :
  Parser_syntax.exp -> Interpreter.strictness_flag -> Interpreter.funcbody

val coq_syntax_from_file : string -> Interpreter.prog
val coq_syntax_from_string : string -> Interpreter.prog

