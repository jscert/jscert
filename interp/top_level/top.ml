module Environment =
struct
  
  let _ = Parser_main.init ()
  
  let (get, set, up) =
    let compt = ref 0 in
      ((fun () -> !compt),
      (fun x -> compt := x),
      (fun () -> incr compt; !compt));; 
  
  type env = {
    runs_type : JsInterpreter.runs_type;
    state : JsSyntax.state;
    context : JsSyntax.execution_ctx;
    prog : string;
    file : bool;
    step : bool
  };;
  
  let init () = {
    runs_type = JsInterpreter.runs max_int;
    state = JsInit.state_initial;
    context = JsCommon.execution_ctx_initial false;
    prog = "";
    file = false;
    step = false
  };;
  
  let add env s = {
    runs_type = env.runs_type;
    state = env.state;
    context = env.context;
    prog = env.prog ^ s;
    file = false;
    step = env.step
  };;
  
  let clear env = {
    runs_type = env.runs_type;
    state = env.state;
    context = env.context;
    prog = "";
    file = false;
    step = env.step
  };;
  
  let load env file = {
    runs_type = env.runs_type;
    state = env.state;
    context = env.context;
    prog = file;
    file = true;
    step = env.step
  };;
  
  let reset env = {
    runs_type = env.runs_type;
    state = JsInit.state_initial;
    context = env.context;
    prog = env.prog;
    file = false;
    step = env.step
  };;
  
  let step env = {
    runs_type = JsInterpreter.runs (up ());
    state = env.state;
    context = env.context;
    prog = env.prog;
    file = env.file;
    step = true
  };;
  
  let unstep env = {
    runs_type = JsInterpreter.runs max_int;
    state = env.state;
    context = env.context;
    prog = env.prog;
    file = env.file;
    step = false
  };;
  
  let update env state = {
    runs_type = if env.step then JsInterpreter.runs (up ()) else JsInterpreter.runs max_int;
    state = state;
    context = env.context;
    prog = "";
    file = false;
    step = env.step
  };;
  
  let dump state = (*Prheap.prheap true state.JsSyntax.state_object_heap*)
    Prheap.prstate true state;;
  
  let translate_file file = Translate_syntax.coq_syntax_from_file file;;
  let translate_string str = Translate_syntax.coq_syntax_from_string str;;

  let launch runs state ctx prog =
    JsInterpreterMonads.if_void
      (JsInterpreter.execution_ctx_binding_inst runs state ctx JsSyntax.Coq_codetype_global None prog [])
      (fun s' -> runs.JsInterpreter.runs_type_prog s' ctx prog)
  
  let eval env =
    let prog = if env.file then
      translate_file env.prog
    else
      translate_string env.prog in
      launch env.runs_type env.state env.context prog;; 
  
  class environment e = object
    val env : env = e
    method add s = new environment (add env s)
    method clear = new environment (clear env)
    method dump = dump env.state
    method eval = eval env
    method load f = new environment (load env f)
    method reset = new environment (reset env)
    method step = set 0; new environment (step env)
    method update s = set 0; new environment (update env s)
    method unstep = new environment (unstep env)
    method next s = if env.step then
      (new environment (step env),
      (dump s) ^ (Printf.sprintf "\nStep %i, enter to continue..." (get ())))
    else
      (new environment (clear env), "Bottom")
  end;;

  let create () = new environment (init ());;
  
end;;


let command_help =
"
List of commands:
#dump: dump the memory state
#help: print this list of commands
#load: load a file and launch the interpreter
#quit: quit the top-level
#reset: reset the state to the initial state
#step: step-by-step mode available
#unstep: step-by-step mode disable
"
  
let print res =
   (Prheap.prrestype res.JsSyntax.res_type) ^ "; " ^ (Prheap.prresvalue res.JsSyntax.res_value)

let display env = try 
    (match env#eval with
     | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_val (_, _)) ->
       env#clear, "**Impossible**"
     | JsInterpreterMonads.Coq_result_some (JsSyntax.Coq_specret_out o) ->
       begin match o with
         | JsSyntax.Coq_out_div ->  env#clear, "Diverge"
         | JsSyntax.Coq_out_ter (state, res) -> 
           (*print_endline (Prheap.prstate false state);*)
           env#update state, print res
       end
     | JsInterpreterMonads.Coq_result_not_yet_implemented -> env#clear, "Not yet implemented"
     | JsInterpreterMonads.Coq_result_impossible ->  env#clear, "Impossible"
     | JsInterpreterMonads.Coq_result_bottom bot ->  env#next bot)
  with
  | Xml.File_not_found s -> env#clear, "Xml: File not found..."
  | Parser.InvalidArgument -> env#clear, "Parser: Invalid Argument...";;

let rec read env = scan env (read_line ())

and scan env = function
  | "" -> let (env, str) = display env in Printf.printf "%s\n\n< " str; read env
  | s -> begin match s.[0] with
    | '#' -> command env s
    | _ -> print_string "< "; read (env#add ("\n"^s))
  end

and command env str = Scanf.sscanf str "# %s %s " (fun s s' -> match s with
  | "dump" -> Printf.printf "%s\n\n< " env#dump; read env
  | "help" -> Printf.printf "%s\n\n< " command_help; read env
  | "load" -> let (env, str) = display (env#load s') in Printf.printf "%s\n\n< " str; read env#clear
  | "quit" -> print_newline ()
  | "reset" -> print_string "State reinitialised to the initial state\n\n< "; read env#reset
  | "step" -> print_string "Step-by-step mode available\n\n< "; read env#step
  | "unstep" -> print_string "Step-by-step mode disable\n\n< "; read env#unstep
  | _ -> Printf.printf "Unknown command %s\n%s\n< " str command_help; read env);;



let () =
  let env = Environment.create () in
  command env "#help";;
