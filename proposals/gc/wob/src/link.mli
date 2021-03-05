val get_inst : (string -> Wasm.Instance.module_inst option) ref

exception Error of Source.region * string

val link : Wasm.Ast.module_ -> Wasm.Instance.module_inst
