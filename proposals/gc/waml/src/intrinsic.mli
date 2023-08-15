type ctxt = Lower.ctxt

val compile_mem : 'a Emit.ctxt -> int32
val compile_mem_alloc : 'a Emit.ctxt -> int32
val compile_text_new : ctxt -> int32
val compile_text_cpy : ctxt -> int32
val compile_text_cat : ctxt -> int32
val compile_text_eq : ctxt -> int32

val compile_func_apply : int -> ctxt -> int32

val compile_load_arg : ctxt -> Source.region -> int -> int32 -> int32 option -> unit
val compile_push_args : ctxt -> Source.region -> int -> (int -> unit) -> unit
