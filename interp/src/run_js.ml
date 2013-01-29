let file = ref ""
let test_prelude = ref ""
let test = ref false

let arguments () =
  let usage_msg="Usage: -jsparser <path> -file <path>" in
  Arg.parse
    [ "-jsparser",
      Arg.String(fun f -> Parser_main.js_to_xml_parser := f),
      "path to js_parser.jar";
      "-file",
      Arg.String(fun f -> file := f),
      "file to run";
      "-verbose",
      Arg.Unit(fun () -> Parser_main.verbose := true),
      "print the parsed program";
      "-test_prelude",
      Arg.String(fun f -> test_prelude := f; test := true),
      "run the given test";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let get_value_ref state r =
	match Interpreter.ref_get_value state (Interpreter.Resvalue_ref r) with
    | Interpreter.Result_normal (
	   Interpreter.Out_ter (_,
	     { Interpreter.res_type = Interpreter.Restype_normal ;
		   Interpreter.res_value =
			 Interpreter.Resvalue_value v })) ->
		Some v
	| _ -> None

let get_global_value state name =
	let x = Translate_syntax.string_to_coq name in
	let r =
	  Interpreter.ref_create_env_loc
	    Interpreter.env_loc_global_env_record
		x true in
	get_value_ref state r

let pr_test state =
  (match get_global_value state "__$ERROR__" with
     | Some v ->
    	  print_endline ("\nA variable [__$ERROR__] is defined at global scope.  Its value is:\n\t"
		  ^ Prheap.prvalue v ^ "\n") ;
		  if !test then exit 1
     | None ->
	    if (not !test) then
	      print_endline "No variable [__$ERROR__] is defined at global scope.\n")


let _ =
  arguments ();
  let exit_if_test _ = if !test then exit 1 in
  try
    let exp = Translate_syntax.coq_syntax_from_file !file in
    let sti = if (!test) then
                begin
                  match Interpreter.run_prog
                          max_int
                          Interpreter.state_initial
                          (Interpreter.execution_ctx_initial false)
                          (Translate_syntax.coq_syntax_from_file !test_prelude)
                  with
                  | Interpreter.Result_normal (
                      Interpreter.Out_ter (state,
						{ Interpreter.res_type = Interpreter.Restype_normal ;
						  Interpreter.res_value =
						    Interpreter.Resvalue_empty })) ->
                     state
                  | _ -> assert false
                  end
              else Interpreter.state_initial
    in match Interpreter.run_prog
            max_int
            sti
            (Interpreter.execution_ctx_initial false)
            exp
    with
    | Interpreter.Result_normal o ->
       begin
         match o with
         | Interpreter.Out_ter (state, res) ->
            begin
              match Interpreter.res_type res with
              | Interpreter.Restype_normal ->
                 (if (not !test) then
      		     begin
                     match Interpreter.res_value res with
                     | Interpreter.Resvalue_value v ->
                        print_endline "\n\nResult:\n";
                        print_endline (Prheap.prvalue v)
                     | Interpreter.Resvalue_ref re ->
                        print_endline ("\n\nResult is a reference of name " ^ (* I’ve added this relatively ugly part to get more precisness o the result. -- Martin *)
      	                                   Prheap.string_of_char_list re.Interpreter.ref_name ^
      		                                   " and of value:\n\t" ^
      	                                       (match get_value_ref state re with
      	                                        | Some v -> Prheap.prvalue v
      	                                        | None -> "Unknown!") ^ "\n")
                     | Interpreter.Resvalue_empty ->
                        print_endline "\n\nNo result\n"
				 end;
				 pr_test state)
              | Interpreter.Restype_break ->
				print_endline "\n\nBREAK\n" ;
				exit_if_test ()
              | Interpreter.Restype_continue ->
				print_endline "\n\nCONTINUE\n" ;
				exit_if_test ()
			  | Interpreter.Restype_return ->
				print_endline "\n\nRETURN\n" ;
				exit_if_test ()
              | Interpreter.Restype_throw ->
                 print_endline "\n\nEXCEPTION THROWN\n" ;
                 (match Interpreter.res_value res with
                 | Interpreter.Resvalue_value v ->
                   print_endline (Prheap.prvalue v)
				 | Interpreter.Resvalue_ref _ ->
				   print_endline "With a reference."
				 | Interpreter.Resvalue_empty ->
				   print_endline "No result with this throw.") ;
				 exit_if_test ()
            end
         | Interpreter.Out_div ->
			print_endline "\n\nDIV\n" ;
			exit_if_test ()
       end;
    | Interpreter.Result_stuck ->
		print_endline "\n\nFIXME:  stuck!\n" ;
		exit_if_test ()
	| Interpreter.Result_bottom -> print_endline "\n\nBOTTOM\n"
  with
  | Assert_failure (file, line, col) ->
	print_string ("\nNot implemented code in file `" ^ file ^ "', line " ^ string_of_int line ^ " and column " ^ string_of_int col) ;
	exit 2
  | Translate_syntax.CoqSyntaxDoesNotSupport s ->
	print_string ("\nTranslation of Javascript syntax does not support `" ^ s ^ "' yet.") ;
	exit 2
  | Xml.File_not_found file ->
	print_string ("\nParsing problem with the file `" ^ file ^ "'.") ;
	exit_if_test ()

