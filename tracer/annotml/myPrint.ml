let fname = "trace.log"

let outf = open_out fname

let log ltype =
  Printf.fprintf outf 
    "{type: '%s', file: '%s', start_line: %d, start_col: %d, end_line: %d, end_col: %d},\n"
    ltype

let enter_call = log "enter_call"
let exit_call = log "exit_call"

let () = at_exit (fun () -> close_out outf)
