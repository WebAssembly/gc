module W :
sig
  module Wasm = Wasm
  include module type of Wasm
  include module type of Wasm.Ast
  include module type of Wasm.Types
  include module type of Wasm.Value
  include module type of Wasm.Operators
  type region = Wasm.Source.region
end


(* Compilation context *)

type internal
type 'a ctxt = {ext : 'a; int : internal}

val make_ctxt : 'a -> 'a ctxt


(* Lookup *)

val lookup_sub_type : 'a ctxt -> int32 -> W.sub_type
val lookup_func_type : 'a ctxt -> int32 -> W.func_type
val lookup_param_type : 'a ctxt -> int32 -> int32 -> W.val_type
val lookup_field_type : 'a ctxt -> int32 -> int32 -> W.val_type
val lookup_ref_field_type : 'a ctxt -> int32 -> int32 -> int32

val lookup_intrinsic : 'a ctxt -> string -> ((int32 -> unit) -> int32) -> int32


(* Emitter *)

val emit_type : 'a ctxt -> W.region -> W.sub_type -> int32
val emit_type_deferred : 'a ctxt -> W.region -> int32 * (W.sub_type -> unit)

val emit_func_import :
  'a ctxt -> W.region -> string -> string -> W.func_type -> int32
val emit_global_import :
  'a ctxt -> W.region -> string -> string -> W.mut -> W.val_type -> int32
val emit_memory_import :
  'a ctxt -> W.region -> string -> string -> int32 -> int32 option -> int32

val emit_func_export : 'a ctxt -> W.region -> string -> int32 -> unit
val emit_global_export : 'a ctxt -> W.region -> string -> int32 -> unit
val emit_memory_export : 'a ctxt -> W.region -> string -> int32 -> unit

val emit_param : 'a ctxt -> W.region -> int32
val emit_local : 'a ctxt -> W.region -> W.val_type -> int32
val emit_global :
  'a ctxt -> W.region -> W.mut -> W.val_type -> W.const option -> int32

val emit_memory : 'a ctxt -> W.region -> int32 -> int32 option -> int32
val emit_passive_data : 'a ctxt -> W.region -> string -> int32
val emit_active_data : 'a ctxt -> W.region -> string -> int32 (* address *)

val emit_instr : 'a ctxt -> W.region -> W.instr' -> unit
val emit_block : 'a ctxt -> W.region ->
    (W.block_type -> W.instr list -> W.instr') ->
    W.block_type -> ('a ctxt -> unit) -> unit

val emit_func :
  'a ctxt -> W.region -> W.val_type list -> W.val_type list ->
  ('a ctxt -> int32 -> unit) -> int32
val emit_func_deferred : 'a ctxt -> W.region ->
  int32 *
  ('a ctxt -> W.val_type list -> W.val_type list -> ('a ctxt -> int32 -> unit) -> unit)

val emit_func_ref : 'a ctxt -> W.region -> int32 -> unit
val emit_start : 'a ctxt -> W.region -> int32 -> unit


(* Generation *)

val gen_module : 'a ctxt -> W.region -> W.module_
