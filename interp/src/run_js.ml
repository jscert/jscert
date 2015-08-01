exception AbnormalPreludeTermination of JsInterpreterMonads.result

let file = ref ""
let test_prelude = ref []
let test = ref false
let printHeap = ref false
let skipInit = ref false
let noParasite = ref false

let string_to_list str = (* Does it already exists somewhere? *)
    let l = ref [] in
    let current = ref "" in
    String.iter (fun c ->
      if c = ',' then (
          l := !current :: !l ;
          current := ""
      ) else
        current := !current ^ String.make 1 c
    ) str ;
    !current :: List.rev !l

let arguments () =
  let usage_msg="Usage: -jsparser <path> -file <path>" in
  Arg.parse
    [ "-json",
      Arg.Unit(fun () -> Parser_main.use_json := true),
      "use the JSON parser (Esprima), -jsparser argument is ignored";
      "-from_stdin",
      Arg.Unit(fun () -> Parser_main.from_stdin := true),
      "Get a pre-parsed intermediate representation from stdin, 
       -jsparser and -file arguments are ignored, not recommended for use with XML";
      "-jsparser",
      Arg.String(fun f -> Parser_main.js_to_xml_parser := f),
      "path to js_parser.jar";
      "-file",
      Arg.String(fun f -> file := f),
      "file to run";
      "-verbose",
      Arg.Unit(fun () -> Parser_main.verbose := true),
      "print the parsed program";
      "-test_prelude",
      Arg.String(fun f ->
         test_prelude := !test_prelude @ string_to_list f; test := true),
      "include the given files before runnning the specified file";
      "-print-heap",
      Arg.Unit(fun () -> printHeap := true),
      "print the final state of the heap";
      "-skip-init",
      Arg.Unit(fun () -> skipInit := true),
      "do not print the initial heap";
      "-no-parasite",
      Arg.Unit(fun () -> noParasite := true),
      "do not run interpreter's code without being explicitely asked for";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let get_value_ref state r =
    match JsInterpreter.ref_get_value
        (JsInterpreter.runs max_int)
        state (JsCommon.execution_ctx_initial false)
        (JsSyntax.Coq_resvalue_ref r) with
    | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_val (_, v)) ->
       Some v
    | _ -> None

let get_global_value state name =
    let x = Translate_syntax.string_to_coq name in
    let r =
      JsCommon.ref_create_env_loc
        JsSyntax.env_loc_global_env_record
        x true in
    get_value_ref state r

let pr_test state =
  if not !noParasite then
  match get_global_value state "__$ERROR__" with
  | Some v ->
       print_endline ("\nA variable [__$ERROR__] is defined at global scope.  Its value is:\n\t"
       ^ Prheap.prvalue v ^ "\n") ;
       if !test then exit 1
  | None ->
     if not !test then
       print_endline "No variable [__$ERROR__] is defined at global scope.\n"

let handle_result result =
  let exit_if_test _ = if !test then exit 1 in
  match result with
    | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_val (_, _)) ->
          print_endline "\n\nA `nothing' object has been created.\n" ;
          print_endline "\n\nFIXME:  this should be impossible!\n" ;
          exit_if_test ()
    | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_out o) ->
      begin
        match o with
        | JsSyntax.Coq_out_ter (state, res) ->
          begin
                  if !printHeap then
                    print_endline (Prheap.prstate !skipInit state);
            match JsSyntax.res_type res with
            | JsSyntax.Coq_restype_normal ->
              if not !test then
              begin
                 match JsSyntax.res_value res with
                 | JsSyntax.Coq_resvalue_value v ->
                   print_endline "\n\nResult:\n";
                   print_endline (Prheap.prvalue v)
                 | JsSyntax.Coq_resvalue_ref re ->
                   print_endline
                     ("\n\nResult is a reference of name " ^ (* I’ve added this relatively ugly part to get more precision from the result. -- Martin *)
                          Prheap.string_of_char_list re.JsSyntax.ref_name ^
                          if !noParasite then "" else (
                             " and of value:\n\t" ^
                             (match get_value_ref state re with
                             | Some v -> Prheap.prvalue v
                             | None -> "Unknown!")) ^ "\n")
                 | JsSyntax.Coq_resvalue_empty ->
                   print_endline "\n\nNo result\n"
              end;
              pr_test state
            | JsSyntax.Coq_restype_break ->
                      print_endline "\n\nBREAK\n" ; exit_if_test ()
            | JsSyntax.Coq_restype_continue ->
              print_endline "\n\nCONTINUE\n" ; exit_if_test ()
            | JsSyntax.Coq_restype_return ->
                 print_endline "\n\nRETURN\n" ; exit_if_test ()
            | JsSyntax.Coq_restype_throw ->
              print_endline "\n\nEXCEPTION THROWN\n" ;
              (match JsSyntax.res_value res with
               | JsSyntax.Coq_resvalue_value v ->
                 print_endline ("\tReturned value:\t" ^ Prheap.prvalue v) ;
                 (match v with
                  | JsSyntax.Coq_value_prim _ -> ()
                  | JsSyntax.Coq_value_object l ->
                    print_newline () ;
                    let r = {
                      JsSyntax.ref_base = JsSyntax.Coq_ref_base_type_value v ;
                      JsSyntax.ref_name = Translate_syntax.string_to_coq "__$ERROR__" ;
                      JsSyntax.ref_strict = false } in
                    if not !noParasite then
                      match get_value_ref state r with
                      | Some v' ->
                        print_endline ("Fetching the `__$ERROR__' field of this returned object resulted to:\t" ^ Prheap.prvalue v')
                      | None ->
                        print_endline "No `__$ERROR__' field has been defined in this returned object.")
                         | JsSyntax.Coq_resvalue_ref _ ->
                           print_endline "With a reference."
                         | JsSyntax.Coq_resvalue_empty ->
                           print_endline "No result with this throw.") ;
              pr_test state ; exit_if_test ()
          end
        | JsSyntax.Coq_out_div ->
          print_endline "\n\nDIV\n" ; exit_if_test ()
      end;
    | JsInterpreterMonads.Coq_result_impossible ->
      print_endline "\n\nFIXME:  this should be impossible!\n" ; exit_if_test ()
    | JsInterpreterMonads.Coq_result_not_yet_implemented ->
      print_endline "\n\nNYI:  this has not yet been implemented in Coq!\n" ; exit 2
    | JsInterpreterMonads.Coq_result_bottom s ->
      print_endline ("\n\nBOTTOM\nCurrent state:\n" ^ Prheap.prstate !skipInit s)

let run_prog_with_state state prog = 
                let runs = JsInterpreter.runs max_int in
                let prog' = (JsSyntaxInfos.add_infos_prog JsSyntax.strictness_false prog) in
                let ctx = JsCommon.execution_ctx_initial (JsSyntaxAux.prog_intro_strictness prog') in
                (JsInterpreterMonads.if_void
                  (JsInterpreter.execution_ctx_binding_inst runs state ctx JsSyntax.Coq_codetype_global None prog' [])
                  (fun s' -> runs.JsInterpreter.runs_type_prog s' ctx prog'))

let run_prog_incremental prog_res prog =
  match prog_res with
  | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_out o) ->
    begin
      match o with
      | JsSyntax.Coq_out_ter (state, res) ->
        begin
          match JsSyntax.res_type res with
          | JsSyntax.Coq_restype_normal ->
              (run_prog_with_state state prog)
          | _ -> raise (AbnormalPreludeTermination prog_res) (* to print out a sensible error *)
        end
      | _ -> raise (AbnormalPreludeTermination prog_res) (* to print out a sensible error *)
    end
  | _ -> raise (AbnormalPreludeTermination prog_res) (* to print out a sensible error *)

let _ =
  arguments ();
  let exit_if_test _ = if !test then exit 1 in
  try
    let prog = Translate_syntax.coq_syntax_from_main !file in
    let JsSyntax.Coq_prog_intro (str, el) = prog in
    let exp_prelude = begin
                        let els =
                          List.concat (List.map (fun f ->
                            let JsSyntax.Coq_prog_intro (_, el0) =
                              Translate_syntax.coq_syntax_from_file ~init:true f in
                            el0) !test_prelude) in
                          JsSyntax.Coq_prog_intro (str, els)
                      end in
    let prelude_res = JsInterpreter.run_javascript (JsInterpreter.runs max_int) exp_prelude in
    handle_result (run_prog_incremental prelude_res prog)
  with
  | AbnormalPreludeTermination res ->
    handle_result res;
    exit 2
  | Assert_failure (file, line, col) ->
    print_string (
      "\nNot implemented code in file `" ^ file ^ "', line " ^
      string_of_int line ^ " and column " ^ string_of_int col) ;
    exit 2
  | Translate_syntax.CoqSyntaxDoesNotSupport s ->
    print_string
      ("\nTranslation of Javascript syntax does not support `" ^ s ^ "' yet.") ;
    exit 2
  | Parser.ParserFailure file ->
    print_string ("\nParsing problem with the file `" ^ file ^ "'.") ;
    exit_if_test ()

