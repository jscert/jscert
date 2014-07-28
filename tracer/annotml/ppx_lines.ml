open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident
open Location

let resname = "__res__"

let arg_from_loc loc =
  let f,ls,cs = get_pos_info loc.loc_start in
  let _,le,ce = get_pos_info loc.loc_end in
  ["", Exp.constant (Const_string (Printf.sprintf "%s[%d,%d]..[%d,%d]" f ls cs le ce,None))]

let rec map_expr default mapper expr =
  match expr with 
  | {pexp_desc = Pexp_apply (f, el); pexp_loc = loc} ->
    let orig_expr = 
      (Exp.apply ~loc f (List.map (fun (l,e) -> l, map_expr default mapper e) el)) in
    Exp.sequence ~loc
      (Exp.apply ~loc 
         (Exp.ident (mknoloc (Longident.parse "MyPrint.fstart"))) 
         (arg_from_loc loc))
      (Exp.let_ Nonrecursive [Vb.mk (Pat.var (mknoloc resname)) orig_expr]
         (Exp.sequence ~loc
            (Exp.apply ~loc 
               (Exp.ident (mknoloc (Longident.parse "MyPrint.fend"))) 
               (arg_from_loc loc))
            (Exp.ident (mknoloc (Lident resname)))))
  | x -> default.expr mapper x

let test_mapper argv =
  { default_mapper with expr = map_expr default_mapper; }

let () = run_main test_mapper
