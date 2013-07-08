open Environment;;
open Reference;;


class type lexicalEnvironment =
object

  method getIdentifierReference : string -> bool -> reference
  method newDeclarativeEnvironment : lexicalEnvironment
  
end;;


module type LexicalEnvironmentSig =
sig

  val create : unit -> lexicalEnvironment
  
end;;



module LexicalEnvironment : LexicalEnvironmentSig =
struct

  type lexicalChain = {
    outer : lexicalChain option;
    inner : environmentRecord
  };;
  
  let init () = {
    outer = None;
    inner = EnvironmentRecord.declarative ()
  };;
  
  let rec getIdentifierReference lex name strict = match lex with
    | None -> {base = UndefinedBase; name = name; strict = strict}
    | Some l -> if l.inner#hasBinding name then
        {base = EnvironmentBase l.inner; name = name; strict = strict}
      else
        getIdentifierReference l.outer name strict;;
  
  
  let newDeclarativeEnvironment lex = {
    outer = Some lex;
    inner = EnvironmentRecord.declarative ()
  };;
  
  
  class lexicalEnvironment c =
  object
  
    val chain = c
    
    method getIdentifierReference = getIdentifierReference (Some c)
    method newDeclarativeEnvironment = new lexicalEnvironment (newDeclarativeEnvironment c)
(*
    method newObjectEnvironment
*)
  end;;

  let create () = new lexicalEnvironment (init ())

end;;
