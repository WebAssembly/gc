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
  | Obj of typ * value ref Env.Map.t
  | Func of func
  | Class of func


(* Values *)

val is_ref : value -> bool

val eq : value -> value -> bool

val to_string : value -> string
