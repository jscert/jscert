let file = ref ""

let arguments () =
  let usage_msg="Usage: -jsparser <path> -file <path>" in
  Arg.parse
    [ "-jsparser", 
      Arg.String(fun f -> Parser_main.js_to_xml_parser := f), 
      "path to js_parser.jar";
      "-file",
      Arg.String(fun f -> file := f),
      "file to run"]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg
    
let _ = 
  arguments (); 
  let exp = Translate_syntax.coq_syntax_from_file !file in
  match Interpreter.run_prog 
          Interpreter.max_int 
          Interpreter.init_heap 
          Interpreter.init_scope 
          exp
  with
  | Interpreter.Out_return (heap,
                            Interpreter.Ret_ret_expr (
                                Interpreter.Ret_expr_value res)) ->
     print_endline "\n\nResult:\n";
     print_endline (Prheap.prvalue res)
  | _ -> print_endline "can't print"
