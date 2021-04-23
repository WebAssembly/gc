type ctxt = Lower.ctxt

val compile_text_new : ctxt -> int32
val compile_text_cpy : ctxt -> int32
val compile_text_cat : ctxt -> int32
val compile_text_eq : ctxt -> int32

val compile_apply : ctxt -> int -> int32
val compile_curry : ctxt -> int -> int32

val compile_load_arg : ctxt -> Source.region -> int -> int32 -> int32 option -> unit
val compile_push_args : ctxt -> Source.region -> int -> int32 -> (int -> unit) -> unit
