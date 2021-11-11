val module_name : string

val compile_runtime : unit -> Wasm.Ast.module_

val import_mem_alloc : Lower.ctxt -> int32
val import_text_new : Lower.ctxt -> int32
(*val import_text_cpy : Lower.ctxt -> int32*)
val import_text_cat : Lower.ctxt -> int32
val import_text_eq : Lower.ctxt -> int32
val import_func_apply : int -> Lower.ctxt -> int32
