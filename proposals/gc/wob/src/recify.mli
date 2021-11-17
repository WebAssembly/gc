open Wasm.Types
open Wasm.Source

val recify : sub_type phrase list -> def_type phrase list * Subst.t
