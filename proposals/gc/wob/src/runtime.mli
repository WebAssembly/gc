val module_name : string

val compile_runtime : unit -> Wasm.Ast.module_

val import_mem_alloc : 'a Emit.ctxt -> int32
val import_text_new : 'a Emit.ctxt -> int32
(*val import_text_cpy : 'a Emit.ctxt -> int32*)
val import_text_cat : 'a Emit.ctxt -> int32
val import_text_eq : 'a Emit.ctxt -> int32
val import_rtt_eq : 'a Emit.ctxt -> int32
