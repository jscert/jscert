
exception CoqSyntaxDoesNotSupport of string
exception Empty_list

val string_to_coq : string -> char list

val unary_op_to_coq : Parser_syntax.unary_op -> JsSyntax.unary_op
val arith_op_to_coq : Parser_syntax.arith_op -> JsSyntax.binary_op
val bin_op_to_coq : Parser_syntax.bin_op -> JsSyntax.binary_op

val exp_to_literal : Parser_syntax.exp -> JsSyntax.literal

val exp_to_exp : Parser_syntax.exp -> JsSyntax.expr
val exp_to_stat : Parser_syntax.exp -> JsSyntax.stat
val exp_to_prog : Parser_syntax.exp -> JsSyntax.prog
val exp_to_elem : Parser_syntax.exp -> JsSyntax.element
val exp_to_funcbody :
  Parser_syntax.exp -> JsSyntax.strictness_flag -> JsSyntax.funcbody

val coq_syntax_from_file : ?init:bool -> string -> JsSyntax.prog
val coq_syntax_from_string : string -> JsSyntax.prog
val coq_syntax_from_main : string -> JsSyntax.prog
