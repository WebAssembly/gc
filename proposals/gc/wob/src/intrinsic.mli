val compile_text_type : 'a Emit.ctxt -> int32
val compile_rtt_type : 'a Emit.ctxt -> int32

val compile_mem : 'a Emit.ctxt -> int32
val compile_mem_alloc : 'a Emit.ctxt -> int32
val compile_text_new : 'a Emit.ctxt -> int32
val compile_text_cpy : 'a Emit.ctxt -> int32
val compile_text_cat : 'a Emit.ctxt -> int32
val compile_text_eq : 'a Emit.ctxt -> int32
val compile_rtt_eq : 'a Emit.ctxt -> int32
