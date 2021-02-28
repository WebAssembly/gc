type var = string

type cls
type typ =
  | Var of var * typ list
  | Null
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Obj
  | Tup of typ list
  | Array of typ
  | Func of var list * typ list * typ list
  | Inst of cls * typ list
  | Class of cls

type con = typ list -> typ
type env


(* Helpers *)

val var : var -> typ


(* Environments *)

val empty_env : env

val extend : env -> var -> con -> env
val extend_gnd : env -> var -> typ -> env
val extend_abs : env -> var -> env

val adjoin_env : env -> env -> env

val lookup : env -> var -> con option


(* Classes *)

val gen_class : var -> var list -> cls
val def_class : cls -> typ -> unit
val eq_class : cls -> cls -> bool


(* Equivalence and Subtyping *)

val eq : typ -> typ -> bool
val sub : typ -> typ -> bool
