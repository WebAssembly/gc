val get_inst : (Source.region -> string -> Wasm.Instance.module_inst option) ref

exception Error of Source.region * string

val link : Wasm.Ast.module_ -> Wasm.Instance.module_inst
