exception Trap of Source.region * string
exception Crash of Source.region * string

val eval_prog : Value.env -> Syntax.prog -> Value.value * Value.env
