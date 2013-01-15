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
          max_int
          Interpreter.state_initial
          Interpreter.execution_ctx_initial 
          exp
  with
  | Interpreter.Out_interp_normal (
      Interpreter.Out_ter (heap,
                           Interpreter.Res_normal r) ->
      begin
        match r with
        | Interpreter.Ret_or_empty_ret (Interpreter.Ret_value v) ->
           print_endline "\n\nResult:\n";
           print_endline (Prheap.prvalue v)
        | Interpreter.Ret_or_empty_ret (Interpreter.Ref re) ->
           print_endline "\n\nResult is a ref\n";
        | Interpreter.Ret_er_empty_empty -> 
           print_endline "\n\nNo result\n"
      end
  | _ -> print_endline "can't print"
