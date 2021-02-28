type var = Syntax.var
type typ = Syntax.typ

and env
and con = typ list -> typ
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
  | Obj of typ * env
  | Func of func
  | Class of func

val string_of_value : value -> string

val empty_env : env
val val_env : var -> value -> env
val typ_env : var -> con -> env

val extend_val : env -> var -> value -> env
val extend_typ : env -> var -> con -> env
val extend_typ_gnd : env -> var -> typ -> env
val extend_typ_abs : env -> var -> env

val adjoin_env : env -> env -> env

val lookup_val : env -> var -> value ref option
val lookup_typ : env -> var -> con option

