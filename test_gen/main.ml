open Environment;;
open Reference;;
open Context;;

let () =

  Random.self_init ();;
  let generator = Statement.create ()
  and channel = open_out "result";;

  let fresh =
    let compt = ref (-1) in
      fun () -> incr compt; string_of_int (!compt);;

  let test = generator#statement in
    List.iter (fun t ->
      let ctx = EnvironmentContext.create () in
        output_string channel (Print.statement "" t);
        output_string channel "\n\n";
        output_string channel (Print.result (Statement.eval ctx t));
        output_string channel "\n\n\n";
        ) test;
    List.iter (fun t ->
      let jvs = open_out ("jvs" ^ (fresh ()) ^ ".js")
      and ctx = EnvironmentContext.create () in
        output_string jvs (Jvs.result (Statement.eval ctx t));
        output_string jvs "\n\n";
        output_string jvs (Jvs.statement "" t);
        close_out jvs;
    ) test;;
    close_out channel;
