
val prbool : bool -> string
val proption : ('a -> string) -> 'a option -> string
val string_of_char_list : char list -> string
val char_list_of_string : string -> char list

val prloc : Interpreter.object_loc -> string
val prenv_loc : Interpreter.env_loc -> string
val prattributes : Interpreter.attributes -> string

val prbinary_op : Interpreter.binary_op -> string
val prmutability : Interpreter.mutability -> string

val prliteral : Interpreter.literal -> string
val prprim : Interpreter.prim -> string
val prvalue : Interpreter.value -> string

val prdescriptor : Interpreter.descriptor -> string
val prfull_descriptor : Interpreter.full_descriptor -> string

val prheap :
  bool (* Skip init *) ->
  (Interpreter.object_loc, Interpreter.object0) Interpreter.Heap.heap ->
  string

val prenv_record :
  (Interpreter.env_loc, Interpreter.env_record) Interpreter.Heap.heap ->
  string

val prstate : bool (* skip init *) -> Interpreter.state -> string

val dump_expr_step : Interpreter.expr -> string
val dump_propbody_step : Interpreter.propbody -> string
val dump_funcbody_step : Interpreter.funcbody -> string
val dump_stat_step : Interpreter.stat -> string
val dump_prog_step : Interpreter.prog -> string

