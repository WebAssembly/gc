exception Mismatch of string * string

val merge : (string * Wasm.Ast.module_) list -> Wasm.Ast.module_ (* raises Mismatch *)
