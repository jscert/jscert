(* TODO:  To be cleaned *)

exception Parser_No_Program
exception Parser_Xml_To_String
exception Parser_Xml_To_Var
exception Parser_Unknown_Tag of (string * int)
exception Parser_PCData
exception Parser_ObjectList
exception JS_To_XML_parser_failure
exception OnlyIntegersAreImplemented
exception Parser_Name_Element
exception Parser_Param_List
exception Unknown_Annotation of string
exception InvalidArgument
exception XmlParserException
exception Unknown_Dec_Inc_Position
exception Parser_Xml_To_Label_Name
exception More_Than_One_Finally
exception Empty_list

val unescape_html : string -> string
val flat_map : ('a -> 'b list) -> 'a list -> 'b list
val get_attr : ('a * 'b) list -> 'a -> 'b

val get_offset : (string * string) list -> int
val get_value : (string * string) list -> string
val get_flags : (string * string) list -> string

val get_label_name : Xml.xml -> string
val string_element : Xml.xml -> string
val name_element : Xml.xml -> string
val remove_annotation_elements : Xml.xml list -> Xml.xml list
val xml_to_vars : Xml.xml -> string list

val get_annot : (string * string) list -> Parser_syntax.annotation

type dec_inc_pos = DI_PRE | DI_POST

val get_dec_inc_pos : (string * string) list -> dec_inc_pos
val get_program_spec_inner : Xml.xml -> Parser_syntax.annotation list
val get_program_spec : Xml.xml -> Parser_syntax.annotation list
val get_annotations : Xml.xml list -> Parser_syntax.annotation list
val get_function_spec : Xml.xml -> Parser_syntax.annotation list
val get_invariant_inner : Xml.xml -> Parser_syntax.annotation list
val get_invariant : Xml.xml -> Parser_syntax.annotation list
val get_xml_child : Xml.xml -> Xml.xml
val get_xml_two_children : Xml.xml -> Xml.xml * Xml.xml
val get_xml_three_children : Xml.xml -> Xml.xml * Xml.xml * Xml.xml

val split_last : 'a list -> 'a * 'a list
val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list

val xml_to_exp : Xml.xml -> Parser_syntax.exp

val var_declaration :
  int -> Xml.xml -> Parser_syntax.var * Parser_syntax.exp option
val parse_array_literal :
  (string * string) list -> Xml.xml list -> Parser_syntax.exp
val parse_unary_op :
  Parser_syntax.unary_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_binary_op :
  Parser_syntax.bin_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_comparison_op :
  Parser_syntax.comparison_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_arith_op :
  Parser_syntax.arith_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_bool_op :
  Parser_syntax.bool_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_assign_op :
  Parser_syntax.arith_op ->
  (string * string) list -> Xml.xml list -> string -> Parser_syntax.exp
val parse_catch_element : Xml.xml -> int -> string * Parser_syntax.exp
val get_catch_finally :
  Xml.xml list ->
  int -> (string * Parser_syntax.exp) option * Parser_syntax.exp option
val parse_case :
  Xml.xml -> int -> Parser_syntax.switch_case * Parser_syntax.exp

