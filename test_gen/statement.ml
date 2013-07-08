open Environment;;
open Reference;;
open Conversion;;

type variable = VariableIdentifier of string
              | VariableInitialiser of string * Expression.t

type block = t list

and variable_statement = variable list

and if_statement = IfThen of Expression.t * t
                 | IfThenElse of Expression.t * t * t

and continue_statement = ContinueEmpty
                       | ContinueIdentifier of target

and break_statement = BreakEmpty
                    | BreakIdentifier of target

and return_statement = ReturnEmpty
                     | ReturnExpression of Expression.t

and try_statement = TryBlockCatch
                  | TryBlockFinally of block * block
                  | TryBlockCatchFinally

and t = Block of block
      | VariableStatement of variable_statement
      | EmptyStatement
      | ExpressionStatement of Expression.t
      | IfStatement of if_statement
      | IterationStatement
      | ContinueStatement of continue_statement
      | BreakStatement of break_statement
      | ReturnStatement of return_statement
      | WithStatement
      | LabelledStatement of string * t
      | SwitchStatement
      | ThrowStatement of Expression.t
      | TryStatement of try_statement
      | DebuggerStatement;;



let eval env =

  let rec block stmt_list =

    let rec iterator sl = function
      | [] -> sl
      | s::l -> begin match sl.rtype with
          | Normal -> iterator (try_eval s sl) l
          | _ -> iterator sl l
        end
    
    and try_eval s sl =
      try
        let s = statement s in
          let v = if s.rvalue = EmptyValue then sl.rvalue else s.rvalue in
          {rtype = s.rtype; rvalue = v; rtarget = s.rtarget}
      with Exception s -> {rtype = Throw; rvalue = Value (String s); rtarget = EmptyTarget}
    
    in
      iterator {rtype = Normal; rvalue = EmptyValue; rtarget = EmptyTarget} stmt_list


  and variable_statement = function
    | [] -> {rtype = Normal; rvalue = EmptyValue; rtarget = EmptyTarget}
    | v :: var_list -> begin match v with
        | VariableIdentifier r -> ()
        | VariableInitialiser (r, e) ->
            putValue (getValue (Expression.eval env e)) (env#identifierResolution r)
      end;
      variable_statement var_list


  and expression_statement e = let e = Expression.eval env e in
    {rtype = Normal; rvalue = e; rtarget = EmptyTarget}
  
  
  and if_statement = function
    | IfThen (e, s) -> begin match toBoolean (getValue (Expression.eval env e)) with
        | Boolean true -> statement s
        | Boolean false -> {rtype = Normal; rvalue = EmptyValue; rtarget = EmptyTarget}
        | _ -> failwith "if_statement"
      end
    | IfThenElse (e, s1, s2) -> begin match toBoolean (getValue (Expression.eval env e)) with
        | Boolean true -> statement s1
        | Boolean false -> statement s2
        | _ -> failwith "if_statement"
      end
  
  
  and continue_statement = function
    | ContinueEmpty -> {rtype = Continue; rvalue = EmptyValue; rtarget = EmptyTarget}
    | ContinueIdentifier i -> {rtype = Continue; rvalue = EmptyValue; rtarget = i}
  
  
  and break_statement = function
    | BreakEmpty -> {rtype = Break; rvalue = EmptyValue; rtarget = EmptyTarget}
    | BreakIdentifier i -> {rtype = Break; rvalue = EmptyValue; rtarget = i}
  
  
  and return_statement = function
    | ReturnEmpty -> {rtype = Return; rvalue = Value (Undefined); rtarget = EmptyTarget}
    | ReturnExpression e -> let e = Expression.eval env e in
        {rtype = Return; rvalue = e; rtarget = EmptyTarget}


  and try_statement = function
    | TryBlockFinally (b, f) -> let b = block b and f = block f in
        if f.rtype = Normal then b else f
    | _ -> failwith "TryStatement not yet implemented"


  and labelled_statement s t =
    let r = statement t in match r.rtype with
      | Break -> if r.rtarget = Ident s then
          {rtype = Normal; rvalue = r.rvalue; rtarget = EmptyTarget}
        else r
      | _ -> r


  and throw_statement e = let e = Expression.eval env e in
    {rtype = Throw; rvalue = e; rtarget = EmptyTarget}


  and statement = function
    | Block b -> block b
    | VariableStatement v -> variable_statement v
    | EmptyStatement -> {rtype = Normal; rvalue = EmptyValue; rtarget = EmptyTarget}
    | ExpressionStatement e -> expression_statement e
    | IfStatement t -> if_statement t
    | ContinueStatement t -> continue_statement t
    | BreakStatement t -> break_statement t
    | ReturnStatement t -> return_statement t
    | LabelledStatement (s, t) -> labelled_statement s t
    | ThrowStatement e -> throw_statement e
    | TryStatement t -> try_statement t
    | _ -> failwith "Statement not yet implemented"

in
  statement;;



(* Generator *)

module type GeneratorSig =
sig
  
  class generator :
  object
  
    method depth : int -> unit
    method statement : t list
  
  end

end;;

module Generator : GeneratorSig =
struct

  let generator = Expression.create ();;


  let random_var () =
    let alphabet = [|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l";
           "m"; "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"|] in
      alphabet.(Random.int 26);;

  let (new_target, random_target, rem_target, clear) =
    let table = Hashtbl.create 257
    and compt = ref 0 in
      ((fun () -> let s = random_var () in
        Hashtbl.add table !compt s; incr compt; s),
      (fun () -> if !compt = 0 then
          EmptyTarget
        else
          let n = Random.int !compt in 
          Ident (Hashtbl.find table n)),
      (fun () -> decr compt; Hashtbl.remove table !compt),
      (fun () -> compt := 0; Hashtbl.reset table))



  let abrupt_completion () = match Random.int 4 with
    | 0 -> begin match random_target () with
        | EmptyTarget -> BreakStatement BreakEmpty
        | Ident s -> BreakStatement (BreakIdentifier (Ident s))
      end
    | 1 -> ContinueStatement ContinueEmpty
    | 2 -> ReturnStatement (ReturnExpression generator#expression)
    | _ -> ThrowStatement generator#expression;;



  let rec block d =
    let rec add = function
      | 0 -> []
      | n -> (statement d) :: (add (n - 1)) in
    add (Random.int 4)

  
  and variable_statement d = 
    let rec add = function
      | 0 -> []
      | n -> (variable (Random.int 2)) :: (add (n - 1))
    and variable = function
      | 0 -> VariableIdentifier (random_var ())
      | _ -> VariableInitialiser (random_var (), generator#expression) in
    add (1 + Random.int 2)
      
  
  and if_statement d = function
    | 0 -> IfThen (generator#expression, statement d)
    | _ -> IfThenElse (generator#expression, statement d, statement d)


  and try_statement d = function
    | 0 -> TryBlockCatch
    | 1 -> TryBlockFinally (block d, block d)
    | _ -> TryBlockCatchFinally


  and statement d =
  
    let random () = match Random.int 6 with
      | 0 -> 0
      | 1 -> 1
      | 2 -> 3
      | 3 -> 4
      | 4 -> 7
      | _ -> 9
    
    and choice d = function
      | 0 -> Block (block (d - 1))
      | 1 -> VariableStatement (variable_statement d)
      | 2 -> EmptyStatement
      | 3 -> ExpressionStatement generator#expression
      | 4 -> IfStatement (if_statement (d - 1) (Random.int 2));
      | 5 -> IterationStatement
      | 6 -> WithStatement
      | 7 -> let t = new_target () in
          let l = LabelledStatement (t, statement (d - 1)) in
            rem_target (); l
      | 8 -> SwitchStatement
      | 9 -> TryStatement (try_statement (d - 1) 1)
      | _ -> abrupt_completion ()
    in
      if d = 0 then ExpressionStatement generator#expression else choice d (random ());;



  let abrupt_block d =
    let rec add = function
      | [] -> [abrupt_completion ()]
      | a :: l -> if Random.bool () then a :: (add l) else a :: (abrupt_completion ()) :: l in
    add (block d);;

  let all_if_statement d = [
    IfStatement (IfThen (generator#expression_true, statement d));
    IfStatement (IfThen (generator#expression_false, statement d));
    IfStatement (IfThenElse (generator#expression_true, statement d, statement d));
    IfStatement (IfThenElse (generator#expression_false, statement d, statement d));
  ];;

  let all_try_statement d = [
    TryStatement (TryBlockFinally (block d, block d));
    TryStatement (TryBlockFinally (block d, abrupt_block d));
    TryStatement (TryBlockFinally (abrupt_block d, block d));
    TryStatement (TryBlockFinally (abrupt_block d, abrupt_block d))
  ];;

  let all_labelled_statement d = [
    (let t = (clear (); new_target ()) in
      LabelledStatement (t, Block (block d)));
    (let t = (clear (); new_target ()) in
      LabelledStatement (t, Block (abrupt_block d)));
  ];;

  class generator =
  object

    val dp = ref 2
    method depth d = dp := d
    method statement = List.concat [
      all_if_statement !dp;
      all_try_statement !dp;
      all_labelled_statement !dp
    ]

  end

end;;

let create () = new Generator.generator;;
