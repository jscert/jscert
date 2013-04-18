
val prbool : bool -> string
val proption : ('a -> string) -> 'a option -> string
val string_of_char_list : char list -> string
val char_list_of_string : string -> char list

val prloc : JsSyntax.object_loc -> string
val prenv_loc : JsSyntax.env_loc -> string
val prattributes : JsSyntax.attributes -> string

val prbinary_op : JsSyntax.binary_op -> string
val prmutability : JsSyntax.mutability -> string

val prliteral : JsSyntax.literal -> string
val prprim : JsSyntax.prim -> string
val prvalue : JsSyntax.value -> string

val prdescriptor : JsSyntax.descriptor -> string
val prfull_descriptor : JsSyntax.full_descriptor -> string

val prheap :
  bool (* Skip init *) ->
  (JsSyntax.object_loc, JsSyntax.coq_object) JsSyntax.Heap.heap ->
  string

val prenv_record :
  (JsSyntax.env_loc, JsSyntax.env_record) JsSyntax.Heap.heap ->
  string

val prstate : bool (* skip init *) -> JsSyntax.state -> string

val dump_expr_step : JsSyntax.expr -> string
val dump_propbody_step : JsSyntax.propbody -> string
val dump_funcbody_step : JsSyntax.funcbody -> string
val dump_stat_step : JsSyntax.stat -> string
val dump_prog_step : JsSyntax.prog -> string

