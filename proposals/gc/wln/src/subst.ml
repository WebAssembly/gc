open Wasm
open Source
open Ast
open Types

module Map = Map.Make(Int32)

type space = int32 Map.t

type t =
{
  stype : space;
  sglobal : space;
  stable : space;
  smemory : space;
  sfunc : space;
  selem : space;
  sdata : space;
  slocal : space;
  slabel : space;
}


(* Constructors *)

let empty : t =
{
  stype = Map.empty;
  sglobal = Map.empty;
  stable = Map.empty;
  smemory = Map.empty;
  sfunc = Map.empty;
  selem = Map.empty;
  sdata = Map.empty;
  slocal = Map.empty;
  slabel = Map.empty;
}

let add_type s x y = {s with stype = Map.add x y s.stype}
let add_global s x y = {s with sglobal = Map.add x y s.sglobal}
let add_table s x y = {s with stable = Map.add x y s.stable}
let add_memory s x y = {s with smemory = Map.add x y s.smemory}
let add_func s x y = {s with sfunc = Map.add x y s.sfunc}
let add_elem s x y = {s with selem = Map.add x y s.selem}
let add_data s x y = {s with sdata = Map.add x y s.sdata}
let add_local s x y = {s with slocal = Map.add x y s.slocal}
let add_label s x y = {s with slabel = Map.add x y s.slabel}

let union_space = Map.union (fun _ _ _ -> assert false)
let union (s1 : t) (s2 : t) : t =
{
  stype = union_space s1.stype s2.stype;
  sglobal = union_space s1.sglobal s2.sglobal;
  stable = union_space s1.stable s2.stable;
  smemory = union_space s1.smemory s2.smemory;
  sfunc = union_space s1.sfunc s2.sfunc;
  selem = union_space s1.selem s2.selem;
  sdata = union_space s1.sdata s2.sdata;
  slocal = union_space s1.slocal s2.slocal;
  slabel = union_space s1.slabel s2.slabel;
}


(* Apply *)

let lookup s x =
  match Map.find_opt x s with
  | Some x' -> x'
  | None -> x

let idx s x = lookup s x.it @@ x.at
let type_idx s = idx s.stype
let global_idx s = idx s.sglobal
let table_idx s = idx s.stable
let memory_idx s = idx s.smemory
let func_idx s = idx s.sfunc
let elem_idx s = idx s.selem
let data_idx s = idx s.sdata
let local_idx s = idx s.slocal
let label_idx s = idx s.slabel

let shift n s =
  Map.fold Int32.(fun x y s -> Map.add (add x n) (add y n) s) s Map.empty

let opt subst s xo = Option.map (subst s) xo
let list subst s xs = List.map (subst s) xs

let var_type s = function
  | SynVar x -> SynVar (lookup s.stype x)
  | _ -> assert false

let num_type s = function
  | (I32Type | I64Type | F32Type | F64Type) as t -> t

let vec_type s = function
  | V128Type as t -> t

let heap_type s = function
  | ( AnyHeapType | EqHeapType | I31HeapType | DataHeapType | ArrayHeapType
    | FuncHeapType | BotHeapType ) as t -> t
  | DefHeapType x -> DefHeapType (var_type s x)
  | RttHeapType x -> RttHeapType (var_type s x)

let ref_type s = function
  | (nul, t) -> (nul, heap_type s t)

let value_type s = function
  | NumType t -> NumType (num_type s t)
  | VecType t -> VecType (vec_type s t)
  | RefType t -> RefType (ref_type s t)
  | BotType -> BotType

let packed_type s t = t

let storage_type s = function
  | ValueStorageType t -> ValueStorageType (value_type s t)
  | PackedStorageType t -> PackedStorageType (packed_type s t)

let field_type s (FieldType (st, mut)) = FieldType (storage_type s st, mut)

let struct_type s (StructType fts) = StructType (list field_type s fts)
let array_type s (ArrayType ft) = ArrayType (field_type s ft)
let func_type s (FuncType (ts1, ts2)) =
  FuncType (list value_type s ts1, list value_type s ts2)

let str_type s = function
  | StructDefType st -> StructDefType (struct_type s st)
  | ArrayDefType at -> ArrayDefType (array_type s at)
  | FuncDefType ft -> FuncDefType (func_type s ft)

let sub_type s = function
  | SubType (xs, st) -> SubType (List.map (var_type s) xs, str_type s st)

let def_type s = function
  | RecDefType sts -> RecDefType (List.map (sub_type s) sts)

let global_type s (GlobalType (t, mut)) = GlobalType (value_type s t, mut)
let table_type s (TableType (lim, t)) = TableType (lim, ref_type s t)
let memory_type s (MemoryType lim) = MemoryType lim

let block_type s = function
  | VarBlockType x -> VarBlockType (var_type s x)
  | ValBlockType t -> ValBlockType (opt value_type s t)

let local s (l : local) = value_type s l.it @@ l.at

let rec instr s (e : instr) = instr' s e.it @@ e.at
and instr' s = function
  | Unreachable -> Unreachable
  | Nop -> Nop
  | Drop -> Drop
  | Select tso -> Select (opt (list value_type) s tso)
  | RefNull t -> RefNull (heap_type s t)
  | RefFunc x -> RefFunc (func_idx s x)
  | RefTest op -> RefTest op
  | RefCast op -> RefCast op
  | RefEq -> RefEq
  | I31New -> I31New
  | I31Get op -> I31Get op
  | StructNew (x, op) -> StructNew (type_idx s x, op)
  | StructGet (x, i, op) -> StructGet (type_idx s x, i, op)
  | StructSet (x, op) -> StructSet (type_idx s x, op)
  | ArrayNew (x, op) -> ArrayNew (type_idx s x, op)
  | ArrayGet (x, op) -> ArrayGet (type_idx s x, op)
  | ArraySet x -> ArraySet (type_idx s x)
  | ArrayLen -> ArrayLen
  | RttCanon x -> RttCanon (type_idx s x)
  | Const c -> Const c
  | Test op -> Test op
  | Compare op -> Compare op
  | Unary op -> Unary op
  | Binary op -> Binary op
  | Convert op -> Convert op
  | VecConst v -> VecConst v
  | VecTest op -> VecTest op
  | VecCompare op -> VecCompare op
  | VecUnary op -> VecUnary op
  | VecBinary op -> VecBinary op
  | VecConvert op -> VecConvert op
  | VecShift op -> VecShift op
  | VecBitmask op -> VecBitmask op
  | VecTestBits op -> VecTestBits op
  | VecUnaryBits op -> VecUnaryBits op
  | VecBinaryBits op -> VecBinaryBits op
  | VecTernaryBits op -> VecTernaryBits op
  | VecSplat op -> VecSplat op
  | VecExtract op -> VecExtract op
  | VecReplace op -> VecReplace op
  | Block (bt, es) -> Block (block_type s bt, block s es)
  | Loop (bt, es) -> Loop (block_type s bt, block s es)
  | If (bt, es1, es2) -> If (block_type s bt, block s es1, block s es2)
  | Let (bt, ls, es) ->
    let s' = {s with slocal = shift (Wasm.Lib.List32.length ls) s.slocal} in
    Let (block_type s bt, list local s ls, block s' es)
  | Br x -> Br (label_idx s x)
  | BrIf x -> BrIf (label_idx s x)
  | BrCast (x, op) -> BrCast (label_idx s x, op)
  | BrCastFail (x, op) -> BrCastFail (label_idx s x, op)
  | BrTable (xs, x) -> BrTable (list label_idx s xs, label_idx s x)
  | Return -> Return
  | Call x -> Call (func_idx s x)
  | CallIndirect (x, y) -> CallIndirect (table_idx s x, type_idx s y)
  | CallRef -> CallRef
  | ReturnCallRef -> ReturnCallRef
  | FuncBind x -> FuncBind (type_idx s x)
  | LocalGet x -> LocalGet (local_idx s x)
  | LocalSet x -> LocalSet (local_idx s x)
  | LocalTee x -> LocalTee (local_idx s x)
  | GlobalGet x -> GlobalGet (global_idx s x)
  | GlobalSet x -> GlobalSet (global_idx s x)
  | TableGet x -> TableGet (table_idx s x)
  | TableSet x -> TableSet (table_idx s x)
  | TableSize x -> TableSize (table_idx s x)
  | TableGrow x -> TableGrow (table_idx s x)
  | TableFill x -> TableFill (table_idx s x)
  | TableCopy (x, y) -> TableCopy (table_idx s x, table_idx s y)
  | TableInit (x, y) -> TableInit (table_idx s x, elem_idx s y)
  | ElemDrop x -> ElemDrop (elem_idx s x)
  | Load op -> Load op
  | Store op -> Store op
  | VecLoad op -> VecLoad op
  | VecStore op -> VecStore op
  | VecLoadLane op -> VecLoadLane op
  | VecStoreLane op -> VecStoreLane op
  | MemorySize -> assert (lookup s.smemory 0l = 0l); MemorySize
  | MemoryGrow -> assert (lookup s.smemory 0l = 0l); MemoryGrow
  | MemoryCopy -> assert (lookup s.smemory 0l = 0l); MemoryCopy
  | MemoryFill -> assert (lookup s.smemory 0l = 0l); MemoryFill
  | MemoryInit x -> assert (lookup s.smemory 0l = 0l); MemoryInit (data_idx s x)
  | DataDrop x -> DataDrop (data_idx s x)

and block s (es : instr list) =
  list instr {s with slabel = shift 1l s.slabel} es

let const s (c : const) =
  assert (s.slocal = Map.empty);
  assert (s.slabel = Map.empty);
  block s c.it @@ c.at

let global s (g : global) =
  { gtype = global_type s g.it.gtype;
    ginit = const s g.it.ginit;
  } @@ g.at

let func s (f : func) =
  assert (s.slocal = Map.empty);
  assert (s.slabel = Map.empty);
  { ftype = type_idx s f.it.ftype;
    locals = list local s f.it.locals;
    body = block s f.it.body;
  } @@ f.at

let table s (t : table) = {ttype = table_type s t.it.ttype} @@ t.at
let memory s (m : memory) = {mtype = memory_type s m.it.mtype} @@ m.at

let segment_mode idx s (m : segment_mode) =
  match m.it with
  | Passive -> Passive @@ m.at
  | Declarative -> Declarative @@ m.at
  | Active {index; offset} ->
    Active {index = idx s index; offset = const s offset} @@ m.at

let elem s (e : elem_segment) =
  { etype = ref_type s e.it.etype;
    einit = list const s e.it.einit;
    emode = segment_mode table_idx s e.it.emode;
  } @@ e.at

let data s (d : data_segment) =
  { dinit = d.it.dinit;
    dmode = segment_mode memory_idx s d.it.dmode;
  } @@ d.at

let export_desc s (d : export_desc) =
  match d.it with
  | FuncExport x -> FuncExport (func_idx s x) @@ d.at
  | TableExport x -> TableExport (table_idx s x) @@ d.at
  | MemoryExport x -> MemoryExport (memory_idx s x) @@ d.at
  | GlobalExport x -> GlobalExport (global_idx s x) @@ d.at

let import_desc s (d : import_desc) =
  match d.it with
  | FuncImport x -> FuncImport (type_idx s x) @@ d.at
  | TableImport tt -> TableImport (table_type s tt) @@ d.at
  | MemoryImport mt -> MemoryImport (memory_type s mt) @@ d.at
  | GlobalImport gt -> GlobalImport (global_type s gt) @@ d.at

let export s (e : export) =
  { name = e.it.name;
    edesc = export_desc s e.it.edesc;
  } @@ e.at

let import s (i : import) =
  { module_name = i.it.module_name;
    item_name = i.it.item_name;
    idesc = import_desc s i.it.idesc;
  } @@ i.at

let type_ s (t : type_) = def_type s t.it @@ t.at

let module_ s (m : module_) =
  { types = list type_ s m.it.types;
    globals = list global s m.it.globals;
    tables = list table s m.it.tables;
    memories = list memory s m.it.memories;
    funcs = list func s m.it.funcs;
    start = opt func_idx s m.it.start;
    elems = list elem s m.it.elems;
    datas = list data s m.it.datas;
    imports = list import s m.it.imports;
    exports = list export s m.it.exports;
  } @@ m.at
