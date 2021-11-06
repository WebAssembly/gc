(* Types *)

type var = string

type value =
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Con of var * value list
  | Ref of value ref
  | Fun of ((var * value) list -> value -> value)
  | Pack of module_

and module_ =
  | Str of str
  | Fct of (module_ -> module_)

and str = (value, unit, module_, unit) Env.env


(* Operations *)

val int : int32 -> value
val fix : (var * value) list -> value -> value

val eq : value -> value -> bool

val con : var -> int -> value

val is_bool : value -> bool
val of_bool : bool -> value
val to_bool : value -> bool

val string_of_value : value -> string
val string_of_module : module_ -> string
