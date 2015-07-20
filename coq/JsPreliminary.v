Set Implicit Arguments.
Require Export JsSyntax JsSyntaxAux JsCommon.
Open Scope string_scope.
Open Scope list_scope.

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
(*Implicit Type B : builtin.*)
Implicit Type ty : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.


(**************************************************************)
(** ** Auxiliary definitions used for type conversions (9) *)

(** Converts a number to a boolean *)

Definition convert_number_to_bool n :=
  ifb (n = JsNumber.zero \/ n = JsNumber.neg_zero \/ n = JsNumber.nan)
    then false
    else true.

(** Converts a string to a boolean *)

Definition convert_string_to_bool s :=
  ifb (s = "") then false else true.

(** Convert primitive to boolean *)

Definition convert_prim_to_boolean w :=
  match w with
  | prim_undef => false
  | prim_null => false
  | prim_bool b => b
  | prim_number n => convert_number_to_bool n
  | prim_string s => convert_string_to_bool s
  end.

(** Convert a value to a boolean (9.2) *)

Definition convert_value_to_boolean v :=
  match v with
  | value_prim p => convert_prim_to_boolean p
  | value_object _ => true
  end.

(** Convert primitive to number (9.3) *)

Definition convert_prim_to_number w :=
  match w with
  | prim_undef => JsNumber.nan
  | prim_null => JsNumber.zero
  | prim_bool b => if b then JsNumber.one else JsNumber.zero
  | prim_number n => n
  | prim_string s => JsNumber.from_string s
  end.

(** Convert number to integer *)

Definition convert_number_to_integer n :=
  ifb n = JsNumber.nan
    then JsNumber.zero
  else ifb (n = JsNumber.zero \/ n = JsNumber.neg_zero
       \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity)
    then n
  else
    JsNumber.mult (JsNumber.sign n) (JsNumber.floor (JsNumber.absolute n)).

(** Convert primitive to integer (9.4) *)

Definition convert_primitive_to_integer w :=
  convert_number_to_integer (convert_prim_to_number w).

(** Convert boolean to string *)

Definition convert_bool_to_string b :=
  if b then "true" else "false".

(** Convert primitive to string (9.8) *)

Definition convert_prim_to_string w :=
  match w with
  | prim_undef => "undefined"
  | prim_null => "null"
  | prim_bool b => convert_bool_to_string b
  | prim_number n => JsNumber.to_string n
  | prim_string s => s
  end.


(**************************************************************)
(** ** Auxiliary functions for comparisons *)

(** Abstract equality comparison for values of the same type.
    (the code assumes [v1] and [v2] to both have type [ty].) 
    (11.9.3) *)

Definition equality_test_for_same_type ty v1 v2 :=
  match ty with
  | type_undef => true
  | type_null => true
  | type_number =>
     match v1,v2 with
     | value_prim (prim_number n1), value_prim (prim_number n2) =>
       ifb n1 = JsNumber.nan then false
       else ifb n2 = JsNumber.nan then false
       else ifb n1 = JsNumber.zero /\ n2 = JsNumber.neg_zero then true
       else ifb n1 = JsNumber.neg_zero /\ n2 = JsNumber.zero then true
       else decide (n1 = n2)
     | _,_ => false (* this case never happens, by assumption *)
     end
  | type_string => decide (v1 = v2)
  | type_bool => decide (v1 = v2)
  | type_object => decide (v1 = v2)
  end.

(** Strict equality comparison (11.9.6) *)

Definition strict_equality_test v1 v2 :=
  let ty1 := type_of v1 in
  let ty2 := type_of v2 in
  ifb ty1 = ty2
    then equality_test_for_same_type ty1 v1 v2
    else false.

(** Inequality comparison for numbers *)

Definition inequality_test_number n1 n2 : prim :=
  ifb n1 = JsNumber.nan \/ n2 = JsNumber.nan then prim_undef
  else ifb n1 = n2 then false
  else ifb n1 = JsNumber.zero /\ n2 = JsNumber.neg_zero then false
  else ifb n1 = JsNumber.neg_zero /\ n2 = JsNumber.zero then false
  else ifb n1 = JsNumber.infinity then false
  else ifb n2 = JsNumber.infinity then true
  else ifb n2 = JsNumber.neg_infinity then false
  else ifb n1 = JsNumber.neg_infinity then true
  else JsNumber.lt_bool n1 n2.

(** Inequality comparison for strings *)

Fixpoint inequality_test_string s1 s2 : bool :=
  match s1, s2 with
  | _, EmptyString => false
  | EmptyString, String _ _ => true
  | String c1 s1', String c2 s2' =>
     ifb c1 = c2
       then inequality_test_string s1' s2'
       else decide (int_of_char c1 < int_of_char c2)
  end.

(** Inequality comparison (11.8.5) *)

Definition inequality_test_primitive w1 w2 : prim :=
  match w1, w2 with
  | prim_string s1, prim_string s2 => inequality_test_string s1 s2
  | _, _ => inequality_test_number (convert_prim_to_number w1) (convert_prim_to_number w2)
  end.


(**************************************************************)
(** ** Auxiliary definitions for reduction of [typeof] *)

Open Scope string_scope.

(** [typeof] for a primitive *)

Definition typeof_prim w :=
  match w with
  | prim_undef => "undefined"
  | prim_null => "object"
  | prim_bool b => "boolean"
  | prim_number n => "number"
  | prim_string s => "string"
  end.

(** [typeof] for a value (11.4.3) *)

Definition typeof_value S v :=
  match v with
  | value_prim w => typeof_prim w
  | value_object l => If is_callable S l then "function" else "object"
  end.


(**************************************************************)
(** ** Auxiliary definition used by object initializers *)

(** Interpretation of a string as a property name (11.1.5) *)

Definition string_of_propname (pn : propname) : prop_name :=
  match pn with 
  | propname_identifier s => s
  | propname_string s => s
  | propname_number n => JsNumber.to_string n
  end.

(** Interpretation of a native error code as a string (15.11.7.9) *)

Definition string_of_native_error (ne : native_error) :=
  match ne with
  | native_error_eval => "EvalError"
  | native_error_range => "RangeError"
  | native_error_ref => "ReferenceError"
  | native_error_syntax => "SyntaxError"
  | native_error_type => "TypeError"
  | native_error_uri => "URIError"
  end.

