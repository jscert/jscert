open Prheap

(* Various debug helper functions *)

(* Inserted by extraction *)

let not_yet_implemented_because loc s =
  print_endline (loc ^ ": Not implemented because: " ^ string_of_char_list s)

let impossible_because loc s =
  print_endline (loc ^ ": Stuck because: " ^ string_of_char_list s)

let impossible_with_heap_because loc s message =
  print_endline (loc ^ ": Stuck!\nState:  " ^ prstate true s ^ "\nMessage:\t" ^ string_of_char_list message)

(* Inserted into JsInterpreter by patching in Makefile functions named after the appropriate insertion *)

let ref_get_value r =
  prerr_string "Warning: ref_get_value returns the undefined value on ";
  prerr_string (Prheap.prref r);
  prerr_newline()


let ref_get_value_2 r =
  prerr_string ("Warning: ref_get_value returns the undefined value on ");
  prerr_string (Prheap.prresvalue r);
  prerr_newline()

let run_object_method l =
  prerr_endline (Printf.sprintf "Warning: in run_object_method the location %s is unfetchable." (Prheap.prloc l))

let run_object_heap_set_extensible l =
  prerr_endline (Printf.sprintf "Warning: in run_object_heap_set_extensible the location %s is unfetchable." (Prheap.prloc l))

let lexical_env_get_identifier_ref x0 =
  prerr_endline ("Warning: lexical_env_get_identifier_ref fails to find " ^ (Prheap.string_of_char_list x0))

