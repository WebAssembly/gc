(* Types *)

type var = string
type typ = Type.typ

and func = typ list -> value list -> value

and value =
  | Null
  | Bool of bool
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Array of value ref list
  | Obj of typ * (Type.sort * value ref) Env.Map.t ref
  | Func of func
  | Class of Type.cls * func


(* Values *)

val is_ref : value -> bool

val eq : value -> value -> bool

val default : Type.typ -> value

val to_string : value -> string
