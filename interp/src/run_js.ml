let file = ref ""
let test_prelude = ref []
let test = ref false
let printHeap = ref false
let skipInit = ref false

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
      Arg.String(fun f ->
         test_prelude := !test_prelude @ string_to_list f; test := true),
      "include the given files before runnning the specified file.";
      "-print-heap",
      Arg.Unit(fun () -> printHeap := true),
      "print the final state of the heap";
      "-skip-init",
      Arg.Unit(fun () -> skipInit := true),
      "do not print the initial heap";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let get_value_ref state r =
	match JsInterpreter.ref_get_value
		(JsInterpreter.runs max_int)
		state (JsPreliminary.execution_ctx_initial false)
		(JsSyntax.Coq_resvalue_ref r) with
    | JsInterpreter.Coq_result_out (
	   JsSyntax.Coq_out_ter (_,
	     { JsSyntax.res_type = JsSyntax.Coq_restype_normal ;
		   JsSyntax.res_value =
			 JsSyntax.Coq_resvalue_value v })) ->
	   Some v
	| _ -> None

let get_global_value state name =
	let x = Translate_syntax.string_to_coq name in
	let r =
	  JsPreliminary.ref_create_env_loc
	    JsSyntax.env_loc_global_env_record
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
    let exp' = if (!test) then
                begin
					let JsSyntax.Coq_prog_intro (str, el) = exp in
                    let els =
                        List.concat (List.map (fun f ->
					        let JsSyntax.Coq_prog_intro (_, el0) =
						        Translate_syntax.coq_syntax_from_file f in
                            el0) !test_prelude) in
					JsSyntax.Coq_prog_intro (str, els @ el)
                  end
              else exp
    in match JsInterpreter.run_javascript
            max_int
            exp'
    with
    | JsInterpreter.Coq_result_out o ->
       begin
         match o with
         | JsSyntax.Coq_out_ter (state, res) ->
            begin
			  if !printHeap then
			    print_endline
					(Prheap.prstate !skipInit state) ;
              match JsSyntax.res_type res with
              | JsSyntax.Coq_restype_normal ->
                 (if (not !test) then
      		     begin
                     match JsSyntax.res_value res with
                     | JsSyntax.Coq_resvalue_value v ->
                        print_endline "\n\nResult:\n";
                        print_endline (Prheap.prvalue v)
                     | JsSyntax.Coq_resvalue_ref re ->
                        print_endline ("\n\nResult is a reference of name " ^ (* I’ve added this relatively ugly part to get more precisness from the result. -- Martin *)
      	                                   Prheap.string_of_char_list re.JsSyntax.ref_name ^
      		                                   " and of value:\n\t" ^
      	                                       (match get_value_ref state re with
      	                                        | Some v -> Prheap.prvalue v
      	                                        | None -> "Unknown!") ^ "\n")
                     | JsSyntax.Coq_resvalue_empty ->
                        print_endline "\n\nNo result\n"
				 end;
				 pr_test state)
              | JsSyntax.Coq_restype_break ->
				print_endline "\n\nBREAK\n" ;
				exit_if_test ()
              | JsSyntax.Coq_restype_continue ->
				print_endline "\n\nCONTINUE\n" ;
				exit_if_test ()
			  | JsSyntax.Coq_restype_return ->
				print_endline "\n\nRETURN\n" ;
				exit_if_test ()
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
                     match get_value_ref state r with
                     | Some v' ->
                       print_endline ("Fetching the `__$ERROR__' field of this returned object resulted to:\t" ^ Prheap.prvalue v')
                     | None ->
                       print_endline "No `__$ERROR__' field has been defined in this returned object.")
				 | JsSyntax.Coq_resvalue_ref _ ->
				   print_endline "With a reference."
				 | JsSyntax.Coq_resvalue_empty ->
				   print_endline "No result with this throw.") ;
                 pr_test state ;
				 exit_if_test ()
            end
         | JsSyntax.Coq_out_div ->
			print_endline "\n\nDIV\n" ;
			exit_if_test ()
       end;
    | JsInterpreter.Coq_result_impossible ->
		print_endline "\n\nFIXME:  this should be impossible!\n" ;
		exit_if_test ()
    | JsInterpreter.Coq_result_not_yet_implemented ->
		print_endline "\n\nStuck:  this is not implemented yet!\n" ;
        exit 2
	| JsInterpreter.Coq_result_bottom -> print_endline "\n\nBOTTOM\n"
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

