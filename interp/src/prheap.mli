
val prbool : bool -> string
val proption : ('a -> string) -> 'a option -> string
val string_of_char_list : char list -> string
val char_list_of_string : string -> char list

val prlabel : JsSyntax.label -> string
val prlabel_set : JsSyntax.label_set -> string

val prprealloc : JsSyntax.prealloc -> string
val prcall : JsSyntax.call -> string
val prconstruct : JsSyntax.construct -> string
val prhas_instance : JsSyntax.builtin_has_instance -> string
val prget : JsSyntax.builtin_get -> string
val prdelete : JsSyntax.builtin_delete -> string

val prloc : JsSyntax.object_loc -> string
val prprop_name : char list -> string
val prenv_loc : JsSyntax.env_loc -> string
val prlexical_env : JsSyntax.lexical_env -> string
val prattributes : JsSyntax.attributes -> string

val prbinary_op : JsSyntax.binary_op -> string
val prmutability : JsSyntax.mutability -> string

val prliteral : JsSyntax.literal -> string
val prprim : JsSyntax.prim -> string
val prvalue : JsSyntax.value -> string
val prref : JsSyntax.ref -> string
val prresvalue : JsSyntax.resvalue -> string

val prdescriptor : JsSyntax.descriptor -> string
val prfull_descriptor : JsSyntax.full_descriptor -> string

val probject_properties : JsSyntax.object_properties_type -> string

val prheap :
  bool (* Skip init *) ->
  (JsSyntax.object_loc, JsSyntax.coq_object) JsSyntax.Heap.heap ->
  string

val prenv_record :
  (JsSyntax.env_loc, JsSyntax.env_record) JsSyntax.Heap.heap ->
  string

val prstate : bool (* skip init *) -> JsSyntax.state -> string
val formatterstate : Format.formatter -> JsSyntax.state -> unit
val prrestype : JsSyntax.restype -> string

val dump_expr_step : JsSyntax.expr -> string
val dump_propbody_step : JsSyntax.propbody -> string
val dump_funcbody_step : JsSyntax.funcbody -> string
val dump_stat_step : JsSyntax.stat -> string
val dump_prog_step : JsSyntax.prog -> string

