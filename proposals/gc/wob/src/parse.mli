type start = Prog | Repl

exception Error of Source.region * string

val parse : string -> Lexing.lexbuf -> start -> Syntax.prog (* raises Syntax *)

val prog_of_string : string -> Syntax.prog (* raises Syntax *)
