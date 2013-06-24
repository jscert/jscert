{

  (* This preprocessor removes all comments and proofs in a Coq file. *)

  (* There are some exceptions, though. Proofs that end with "Defined."
     are kept, as the proof term is important in that case. Proofs that
     are found within a section are kept, as the proof term is used to
     drive parameterization when the section is closed. *)

  (* Care is taken to preserve every newline character in the original
     file, so as to not affect the line numbering. *)

  open Printf
  open Lexing

  (* The name of the source file. *)
  let filename =
    ref None

  (* Keep comments? *)
  let kc =
    ref false

  (* Keep proofs? *)
  let kp =
    ref false

  let spec =
    Arg.align [
      "--keep-comments", Arg.Set kc, " Keep comments (by default, they are removed)";
      "--keep-proofs", Arg.Set kp, " Keep proofs (by default, they are removed)";
    ]

  let () =
    Arg.parse spec (fun name -> filename := Some name) "Usage:"

  let filename =
    match !filename with
    | None ->
	Arg.usage spec "Usage:";
	exit 1
    | Some name ->
	name

  (* Error reporting. -- Arthur tried to improved but failed *)

  let string_of_pos p =
    sprintf "File %s, line %d, character %d" p.pos_fname p.pos_lnum p.pos_bol

  let warning lexbuf msg =
    (* fprintf stderr "coqj: %s: character %d: %s.\n%!" filename (lexeme_start lexbuf) msg *)
    fprintf stderr "coqj: %s:\n %s.\n%!" (string_of_pos (lexeme_end_p lexbuf)) msg

  let error lexbuf msg =
    (* fprintf stderr "coqj: %s: character %d: %s.\n%!" filename (lexeme_start lexbuf) msg; *)
    fprintf stderr "coqj: %s:\n %s.\n%!" (string_of_pos (lexeme_end_p lexbuf)) msg;
    exit 1

  (* A stack of the sections, modules, and module types that have been opened.
     This stack helps interpret "End" commands. *)
  type scope =
    | Section
    | Other

  let scopes : scope Stack.t =
    Stack.create()

  (* A counter of the currently open sections. *)
  let sections =
    ref 0

  (* A buffer, used while in proof mode. *)
  let b =
    Buffer.create 16384

  (* A counter of how many newline characters are in the above buffer. *)
  let nl =
    ref 0

  (* When in proof mode, output is buffered, otherwise it is echoed directly. *)
  let proof_mode =
    ref false

  let echo lexbuf =
    if !proof_mode then
      Buffer.add_string b (lexeme lexbuf)
    else
      print_string (lexeme lexbuf)

  let newline lexbuf =
    echo lexbuf;
    incr nl

  (* When the end of a proof is reached, the contents of the buffer are either
     shipped out or discarded, according to the parameter [kp]. *)
  let ship kp =
    assert !proof_mode;
    if kp then
      Buffer.output_buffer stdout b
    else begin
      print_string " Admitted.";
      print_string (String.make !nl '\n')
    end;
    Buffer.clear b

}

let newline = ( '\r' | '\n' | '\r' '\n' )

(* Regular mode. *)

rule r = parse
  | "Proof."
  | "Next Obligation." as s
      { if !proof_mode then error lexbuf (sprintf "found \"%s\" while already in proof mode" s);
        assert (Buffer.length b = 0);
        echo lexbuf; proof_mode := true; nl := 0; r lexbuf }
  | "Qed."
      { if not !proof_mode then error lexbuf (sprintf "found \"%s\" while not in proof mode" (lexeme lexbuf));
        echo lexbuf; ship (!kp || !sections > 0); proof_mode := false; r lexbuf }
  | "Admitted." (* Arthur modif: accept Admitted without Proof *)
  | "Abort."
      { proof_mode := true; echo lexbuf; ship (!kp || !sections > 0); proof_mode := false; r lexbuf }
  | "Defined."
      { if not !proof_mode then error lexbuf (sprintf "found \"%s\" while not in proof mode" (lexeme lexbuf));
        echo lexbuf; ship true; proof_mode := false; r lexbuf }
  | "(*"
      { if !kc then echo lexbuf; c lexbuf; r lexbuf }
  | '"'
      { echo lexbuf; s lexbuf; r lexbuf }
  | "Hint"
  | "Ltac"
      { if !proof_mode then warning lexbuf "avoid defining hints or tactics within proofs";
        echo lexbuf; r lexbuf }
  | "Section"
      { Stack.push Section scopes; incr sections; echo lexbuf; r lexbuf }
  | "Module"
  | "Module Type"
      { Stack.push Other scopes; echo lexbuf; r lexbuf }
  | "End"
      { begin try
	  match Stack.pop scopes with Section -> decr sections | Other -> ()
        with Stack.Empty ->
	  warning lexbuf "unmatched \"End\""
        end;
        echo lexbuf; r lexbuf }
  | newline
      { newline lexbuf; r lexbuf }
  | _
      { echo lexbuf; r lexbuf }
  | eof
      { if !proof_mode then warning lexbuf "end-of-file reached while in proof mode" }

(* String literal mode. *)

and s = parse
  | '"' 
      { echo lexbuf }
  | newline
      { newline lexbuf; s lexbuf }
  | '\\' '"'
  | '\\' '\\'
  | _
      { echo lexbuf; s lexbuf }
  | eof
      { error lexbuf "unterminated string" }

(* Comment mode. *)

and c = parse
  | "(*"
      { if !kc then echo lexbuf; c lexbuf; c lexbuf }
  | "*)"
      { if !kc then echo lexbuf }
  | newline
      { newline lexbuf; c lexbuf }
  | _
      { if !kc then echo lexbuf; c lexbuf }
  | eof
      { error lexbuf "unterminated comment" }

(* Main program. *)

{

  let () =
    r (from_channel (open_in filename));
    flush stdout

}
