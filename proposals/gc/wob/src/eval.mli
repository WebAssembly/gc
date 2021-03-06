type env = (Type.sort * Value.value ref, Type.con) Env.env

exception Trap of Source.region * string
exception Crash of Source.region * string

val get_env : (Source.region -> string -> env) ref

val eval_prog : env -> Syntax.prog -> Value.value * env
