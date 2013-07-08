open Environment;;


type base = UndefinedBase
          | BooleanBase of bool
          | NumberBase of float
          | StringBase of string
          | ObjectBase
          | EnvironmentBase of environmentRecord;;

type reference = {base : base; name : string; strict : bool}


type completion = Normal | Break | Continue | Return | Throw;;
type value = Value of primary | Reference of reference | EmptyValue;;
type target = Ident of string | EmptyTarget;;

type result = {rtype : completion; rvalue : value; rtarget : target};;



let getBase r = r.base;;

let getReferenceName r = r.name;;

let isStrictReference r = r.strict;;

let hasPrimitiveBase r = match r.base with
  | BooleanBase _ | NumberBase _ | StringBase _ -> true
  | _ -> false

let isPropertyReference r =
  r.base = ObjectBase || hasPrimitiveBase r;;

let isUnresolvableReference r =
  r.base = UndefinedBase;;



let getValue = function
  | EmptyValue -> failwith "getValue"
  | Value p -> p
  | Reference r -> match r.base with
      | UndefinedBase -> raise (Exception "ReferenceError")
      | EnvironmentBase env -> env#getBindingValue r.name r.strict
      | _ -> failwith "GetValue: not yet implemented";;

let putValue value = function
  | Reference r -> begin match r.base with
      | UndefinedBase -> if r.strict then raise (Exception "ReferenceError")
      | EnvironmentBase env -> env#setMutableBinding r.name value r.strict
      | _ -> failwith "PutValue: not yet implemented"
    end
  | _ -> raise (Exception "ReferenceError")
