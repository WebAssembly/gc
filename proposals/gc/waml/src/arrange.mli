open Syntax
open Wasm.Sexpr

val var : var -> sexpr
val typ : typ -> sexpr
val pat : pat -> sexpr
val exp : exp -> sexpr
val dec : dec -> sexpr
val sig_ : sig_ -> sexpr
val mod_ : mod_ -> sexpr
val spec : spec -> sexpr
val prog : prog -> sexpr
