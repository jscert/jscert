exception Exception of string;;

type primary =  Undefined | Null | Boolean of bool | Number of float | String of string | Object;;


class type environmentRecord =
object

  method createMutableBinding : string -> bool -> unit
  method setMutableBinding : string -> primary -> bool -> unit
  method createImmutableBinding : string -> bool -> unit
  method initialiseImmutableBinding : string -> primary -> unit
  method hasBinding : string -> bool
  method deleteBinding : string -> bool
  method getBindingValue : string -> bool -> primary
  method implicitThisValue : primary

end;;



module type EnvironmentRecordSig =
sig

  val declarative : unit -> environmentRecord

end



module EnvironmentRecord : EnvironmentRecordSig =
struct


  type record = {mutable value : primary option; del : bool; mut : bool};;
  
  
  let createMutableBinding table bind del =
    Hashtbl.add table bind {value = Some Undefined; del = del; mut = true};;
  
  let setMutableBinding table bind value strict =
    let v = Hashtbl.find table bind in
      if v.mut then
       v.value <- Some value
      else
        if strict then
          raise (Exception "TypeError");;
  
  let createImmutableBinding table bind del =
    Hashtbl.add table bind {value = None; del = del; mut = false};;
  
  let initialiseImmutableBinding table bind value =
    let v = Hashtbl.find table bind in match v.value with
      | None -> v.value <- Some value
      | _ -> ()
  
  let getBindingValue table bind strict = match (Hashtbl.find table bind).value with
    | None -> if strict then raise (Exception "ReferenceError") else Undefined
    | Some v -> v;;
  
  let deleteBinding table bind =
    try
      if (Hashtbl.find table bind).del then
        (Hashtbl.remove table bind; true)
      else
        false
    with Not_found -> true;;


  class declarativeEnvironmentRecord t =
  object
  
    val table : (string, record) Hashtbl.t = t
    
    method createMutableBinding = createMutableBinding table
    method setMutableBinding = setMutableBinding table
    method createImmutableBinding = createMutableBinding table
    method initialiseImmutableBinding = initialiseImmutableBinding table
    method hasBinding = Hashtbl.mem table
    method getBindingValue = getBindingValue table
    method deleteBinding = deleteBinding table
    method implicitThisValue = Undefined
    
  end


  let declarative () = new declarativeEnvironmentRecord (Hashtbl.create 257);;

end;;
