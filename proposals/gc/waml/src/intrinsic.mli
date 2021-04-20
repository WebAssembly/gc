val compile_text_new : 'a Emit.ctxt -> int32
val compile_text_cpy : 'a Emit.ctxt -> int32
val compile_text_cat : 'a Emit.ctxt -> int32
val compile_text_eq : 'a Emit.ctxt -> int32

val compile_apply : 'a Emit.ctxt -> int -> int32
val compile_curry : 'a Emit.ctxt -> int -> int32

val compile_load_arg : 'a Emit.ctxt -> Source.region ->
  int -> int32 -> int32 option -> unit
val compile_push_args : 'a Emit.ctxt -> Source.region ->
  int -> int32 -> (int -> unit) -> unit
