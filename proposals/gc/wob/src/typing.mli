type env = (Type.sort * Type.typ, Type.kind * Type.con) Env.env

exception Error of Source.region * string

val initial_env : env
val check_prog : env -> Syntax.prog -> Type.typ * env
