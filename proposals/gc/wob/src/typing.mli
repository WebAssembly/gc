type env = (Type.sort * Type.typ, Type.kind * Type.con) Env.env

exception Error of Source.region * string

val get_env : (Source.region -> string -> env) ref

val check_prog : env -> Syntax.prog -> Type.typ * env
