Set Implicit Arguments.
Require Import JsSemanticsAux. (* Martin:  Should proofs files not to be included in the trusted base? *)
Implicit Types h : heap.


(**************************************************************)
(** ** Definition of well-formedness *)

(** [has_some_proto h l] asserts that [l] has a prototype field
    in [h]. We say in this case that [l] is a valid object. *)

Definition has_some_proto h l :=
  indom h l field_proto.

(** [has_null_proto h l] asssert that [l] has a null 
    prototype field in [h]. *)

Definition has_null_proto h l :=
  binds h l field_proto (value_loc loc_null).

(** [protochain h l] asserts that there is a non-cyclic
    prototype chain in [h] starting from object [l] *)

Inductive protochain h : loc -> Prop :=
  | protochain_end : 
     protochain h loc_null 
  | protochain_step : forall l l',  
     binds h l field_proto (value_loc l') ->
     protochain h l' ->
     protochain h l.

(** [ok_scope h s] asserts that the scope [s] contains 
    only valid objects and that the scope is loc_scope-terminated. 
    (this predicate is called "schain" in the paper *)

Inductive ok_scope h : scope -> Prop := 
  | ok_scope_end : 
     ok_scope h (loc_scope::nil)
  | ok_scope_cons : forall l s,
     ok_scope h s ->
     has_some_proto h l ->
     ok_scope h (l::s).

(** LATER: add the following property in addition to [ok_scope h s] :
    [Mem loc_global s] *)

(** [ok_value h v] asserts that [v] is either a basic value,
    a special value, or it is a valid object in [h] *)

Inductive ok_value (h:heap) : value -> Prop :=
  | ok_value_basic : forall v,
      basic_value v ->
      ok_value h v
  | ok_value_loc : forall l,
      has_some_proto h l ->
      ok_value h (value_loc l).

(** The components of [ok_heap h] follow *)

(** (1) for every bound pair [(l,f)], [l] has a prototype chain *)

Definition ok_heap_protochain_def h := forall l f v,
  binds h l f v -> protochain h l.

(** (2) if the heap contains a reference (l, f)  
        (except field_scope and field_body), then this 
        reference must contains either a basic value 
        or a location with a valid prototype *)

Definition ok_heap_ok_value_def h := forall l f v,
  binds h l f v ->   
  not_scope_or_body f ->  
  ok_value h v.

(** (3) if [(l,@this)] is bound to a value [v], then [v] must be a
        location on an object that has a prototype, moreover
        the proto field of [l] must be [null] *)

Definition ok_heap_this_def h := forall l v,
  binds h l field_this v -> 
  exists l',
    v = value_loc l' /\
    has_null_proto h l /\
    has_some_proto h l'.

(** (4) if [(l,@scope)] or [(l,@body)] is bound to a value [v], 
        then [(l,@scope)] must contain a valid scope, and
        [(l,@body)] must contain some body, and the user field
        named "prototype" must contain a location that has a
        prototype or a value *)

Definition ok_heap_function_def h := forall l v,
  (binds h l field_scope v \/ binds h l field_body v) ->
  exists s x e v',
    binds h l field_scope (value_scope s) /\
    binds h l field_body (value_body x e) /\
    binds h l field_normal_prototype  v' /\
    ok_scope h s.

(** (5) loc_null is never bound to anything *)

Definition ok_heap_null_def h := forall f v,
  binds h loc_null f v -> False.

(** (6) There are contraints on special locations *)

 Record ok_heap_special_def h := {
  ok_heap_special_global_this :
    binds h loc_scope field_this loc_global;
  ok_heap_special_global_proto :
    indom h loc_global field_proto;
  ok_heap_special_obj_proto :
    indom h loc_obj_proto field_proto;
  ok_heap_special_function_proto :
    indom h loc_func_proto field_proto }.

(** [ok_heap h] puts all these invariants together *)

Record ok_heap h := {
  ok_heap_protochain : ok_heap_protochain_def h;
  ok_heap_ok_value : ok_heap_ok_value_def h;
  ok_heap_this : ok_heap_this_def h; 
  ok_heap_function : ok_heap_function_def h;
  ok_heap_null : ok_heap_null_def h;
  ok_heap_special : ok_heap_special_def h }.

(** [ok_ret_expr h r] asserts that [r] is either a valid value
    or a valid reference on a valid object *)

Inductive ok_ret_expr (h:heap) : ret_expr -> Prop :=
  | ok_ret_expr_value : forall v,
      ok_value h v ->
      ok_ret_expr h (ret_expr_value v)
  | ok_ret_expr_ref : forall l x,
      (l = loc_null \/ has_some_proto h l) ->
      ok_ret_expr h (ret_expr_ref (Ref l (field_normal x))).

(** [extends_proto h h'] states that if [l] has a prototype 
    in [h] then it also has a prototype in [h']. *)

Definition extends_proto (h h' : heap) :=
  forall l, has_some_proto h l -> has_some_proto h' l.

