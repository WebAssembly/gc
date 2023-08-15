open Wasm.Types
open Wasm.Source

val recify : sub_type phrase list -> rec_type phrase list * Subst.t
