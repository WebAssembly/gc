open Syntax
open Wasm.Sexpr

val var : var -> sexpr
val typ : typ -> sexpr
val exp : exp -> sexpr
val dec : dec -> sexpr
val prog : prog -> sexpr
