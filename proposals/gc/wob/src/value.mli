(* Types *)

type typ = Type.typ

and func = (Type.sort * value) Env.Map.t -> typ list -> value list -> value

and value =
  | Null
  | Bool of bool
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Box of value
  | Tup of value list
  | Array of value ref list
  | Obj of typ * obj
  | Func of func
  | Class of Type.cls * func * cls

and obj = (Type.sort * value ref) Env.Map.t ref
and cls = (Type.sort * value) Env.Map.t -> typ -> typ list -> value list -> value * (unit -> unit)


(* Accessors *)

val as_obj : value -> obj


(* Recursive closure *)

val fix : (Type.sort * value) Env.Map.t -> value -> value


(* Operations *)

val eq : value -> value -> bool

val default : typ -> value

val to_string : value -> string
