
let write_file filename strl =
    let oc = open_out filename in
    let () = List.iter (output_string oc) strl in
    close_out oc


let load_file f =
    let ic = try open_in f with _ -> failwith ("Error while reading file “" + f + "”.") in
    let n = in_channel_length ic in
    let s = String.create n in
    really_input ic s 0 n ;
    close_in ic ;
    s

let fileList = (* Every argument from the third to all the other ones. *)
    let rec aux i =
        if i >= Array.length Sys.argv then []
        else Sys.argv.(i) :: aux (i + 1)
    in aux 3


let _ =
    let fileTrace = Sys.argv.(1) in
    let fileOut = Sys.argv.(2) in
    write_file fileOut (
            "var tracer_items = [\n" ::
            load_file fileTrace ::
            "\n];\n\nvar tracer_files = {\n" ::
            List.(concat (map (fun f ->
                let rep s1 s2 s3 =
                    Str.(global_replace (regexp (quote s1)) s2 s3)
                in "\t" :: f :: ": \"" ::
                    fold_left (fun s (s1, s2) ->
                        rep s1 s2 s) (load_file f)
                        ["\"", "\\\"";
                         "\r", "";
                         "\n", "\\n";
                         "\\", "\\\\"]
                :: "\",\n" :: []
                ) fileList)) @
                "}\n" :: []
        )

