(* Types *)

type value =
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Con of string * value list
  | Ref of value ref
  | Fun of ((string * value) list -> value -> value)

type module_ =
  | Str of (string * value) list * (string * module_) list
  | Fct of (module_ -> module_)


(* Operations *)

val close : (string * value) list -> value -> value

val eq : value -> value -> bool

val con : string -> int -> value

val is_bool : value -> bool
val of_bool : bool -> value
val to_bool : value -> bool
val to_string : value -> string
