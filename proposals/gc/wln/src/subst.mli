open Wasm

module Map : Map.S with type key = int32

type space = int32 Map.t

type t =
{ stype : space;
  sglobal : space;
  stable : space;
  smemory : space;
  sfunc : space;
  selem : space;
  sdata : space;
  slocal : space;
  slabel : space;
}

val empty : t
val union : t -> t -> t
val add_type : t -> int32 -> int32 -> t
val add_global : t -> int32 -> int32 -> t
val add_table : t -> int32 -> int32 -> t
val add_memory : t -> int32 -> int32 -> t
val add_func : t -> int32 -> int32 -> t
val add_elem : t -> int32 -> int32 -> t
val add_data : t -> int32 -> int32 -> t
val add_local : t -> int32 -> int32 -> t
val add_label : t -> int32 -> int32 -> t

val type_idx : t -> Ast.idx -> Ast.idx
val global_idx : t -> Ast.idx -> Ast.idx
val table_idx : t -> Ast.idx -> Ast.idx
val memory_idx : t -> Ast.idx -> Ast.idx
val func_idx : t -> Ast.idx -> Ast.idx
val elem_idx : t -> Ast.idx -> Ast.idx
val data_idx : t -> Ast.idx -> Ast.idx
val local_idx : t -> Ast.idx -> Ast.idx
val label_idx : t -> Ast.idx -> Ast.idx

val instr : t -> Ast.instr -> Ast.instr
val block : t -> Ast.instr list -> Ast.instr list
val const : t -> Ast.const -> Ast.const

val type_ : t -> Ast.type_ -> Ast.type_
val global : t -> Ast.global -> Ast.global
val func : t -> Ast.func -> Ast.func
val table : t -> Ast.table -> Ast.table
val memory : t -> Ast.memory -> Ast.memory
val elem : t -> Ast.elem_segment -> Ast.elem_segment
val data : t -> Ast.data_segment -> Ast.data_segment
val export : t -> Ast.export -> Ast.export
val import : t -> Ast.import -> Ast.import
val start : t -> Ast.start -> Ast.start

val module_ : t -> Ast.module_ -> Ast.module_

val list : (t -> 'a -> 'a) -> t -> 'a list -> 'a list
