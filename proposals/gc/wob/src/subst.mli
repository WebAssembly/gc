open Wasm

type t

val empty : t
val union : t -> t -> t
val add_type : t -> int32 -> int32 -> t

val module_ : t -> Ast.module_ -> Ast.module_
