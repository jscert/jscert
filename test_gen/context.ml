open Reference;;
open Lexical;;


class type environmentContext =
object

  method identifierResolution : string -> value
  method thisBinding : unit
  
end;;


module type EnvironmentContextig =
sig

  val create : unit -> environmentContext
  
end;;


module EnvironmentContext : EnvironmentContextig =
struct

  type context = {
    lexenv : lexicalEnvironment;
    this : unit
  }
  
  let init () = {
    lexenv = LexicalEnvironment.create ();
    this = ()
  };;
  
  let identifierResolution ctx str =
    Reference (ctx.lexenv#getIdentifierReference str false)
  
  
  class environmentContext c =
  object
  
    val context = c
    
    method identifierResolution = identifierResolution context
    method thisBinding = context.this

  end;;

  let create () = new environmentContext (init ())

end;;
