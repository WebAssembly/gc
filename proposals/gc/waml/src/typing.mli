module T = Type

type env = (T.poly, T.con, T.sig_, T.sig_) Env.env

exception Error of Source.region * string

val get_env : (Source.region -> string -> T.var list * env) ref

val check_prog : env -> Syntax.prog -> T.typ * T.var list * env
