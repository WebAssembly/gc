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

let add_type (s : t) x y = {s with stype = Map.add x y s.stype}
let add_global (s : t) x y = {s with sglobal = Map.add x y s.sglobal}
let add_table (s : t) x y = {s with stable = Map.add x y s.stable}
let add_memory (s : t) x y = {s with smemory = Map.add x y s.smemory}
let add_func (s : t) x y = {s with sfunc = Map.add x y s.sfunc}
let add_elem (s : t) x y = {s with selem = Map.add x y s.selem}
let add_data (s : t) x y = {s with sdata = Map.add x y s.sdata}
let add_local (s : t) x y = {s with slocal = Map.add x y s.slocal}
let add_label (s : t) x y = {s with slabel = Map.add x y s.slabel}

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
let type_idx (s : t) = idx s.stype
let global_idx (s : t) = idx s.sglobal
let table_idx (s : t) = idx s.stable
let memory_idx (s : t) = idx s.smemory
let func_idx (s : t) = idx s.sfunc
let elem_idx (s : t) = idx s.selem
let data_idx (s : t) = idx s.sdata
let local_idx (s : t) = idx s.slocal
let label_idx (s : t) = idx s.slabel

let shift n s =
  Map.fold Int32.(fun x y s -> Map.add (add x n) (add y n) s) s Map.empty

let opt subst s xo = Option.map (subst s) xo
let list subst s xs = List.map (subst s) xs

let var_type s = function
  | StatX x -> StatX (lookup s.stype x)
  | _ -> assert false

let num_type s = function
  | I32T | I64T | F32T | F64T as t -> t

let vec_type s = function
  | V128T as t -> t

let heap_type s = function
  | AnyHT | EqHT | I31HT | StructHT | ArrayHT | NoneHT
  | FuncHT | NoFuncHT | ExternHT | NoExternHT as t -> t
  | VarHT x -> VarHT (var_type s x)
  | DefHT _ | BotHT -> assert false

let ref_type s = function
  | (nul, t) -> (nul, heap_type s t)

let val_type s = function
  | NumT t -> NumT (num_type s t)
  | VecT t -> VecT (vec_type s t)
  | RefT t -> RefT (ref_type s t)
  | BotT -> BotT

let pack_type s t = t

let storage_type s = function
  | ValStorageT t -> ValStorageT (val_type s t)
  | PackStorageT t -> PackStorageT (pack_type s t)

let field_type s (FieldT (mut, st)) = FieldT (mut, storage_type s st)

let struct_type s (StructT fts) = StructT (list field_type s fts)
let array_type s (ArrayT ft) = ArrayT (field_type s ft)
let func_type s (FuncT (ts1, ts2)) =
  FuncT (list val_type s ts1, list val_type s ts2)

let str_type s = function
  | DefStructT st -> DefStructT (struct_type s st)
  | DefArrayT at -> DefArrayT (array_type s at)
  | DefFuncT ft -> DefFuncT (func_type s ft)

let sub_type s = function
  | SubT (fin, hts, st) -> SubT (fin, List.map (heap_type s) hts, str_type s st)

let rec_type s = function
  | RecT sts -> RecT (List.map (sub_type s) sts)

let global_type s (GlobalT (mut, t)) = GlobalT (mut, val_type s t)
let table_type s (TableT (lim, t)) = TableT (lim, ref_type s t)
let memory_type s (MemoryT lim) = MemoryT lim

let block_type s = function
  | VarBlockType x -> VarBlockType (lookup s.stype x.it @@ x.at)
  | ValBlockType t -> ValBlockType (opt val_type s t)

let local s (l : local) = {ltype = val_type s l.it.ltype} @@ l.at

let rec instr s (e : instr) = instr' s e.it @@ e.at
and instr' s = function
  | Unreachable -> Unreachable
  | Nop -> Nop
  | Drop -> Drop
  | Select tso -> Select (opt (list val_type) s tso)
  | RefNull t -> RefNull (heap_type s t)
  | RefIsNull -> RefIsNull
  | RefAsNonNull -> RefAsNonNull
  | RefFunc x -> RefFunc (func_idx s x)
  | RefTest rt -> RefTest (ref_type s rt)
  | RefCast rt -> RefCast (ref_type s rt)
  | RefEq -> RefEq
  | RefI31 -> RefI31
  | I31Get op -> I31Get op
  | StructNew (x, op) -> StructNew (type_idx s x, op)
  | StructGet (x, i, op) -> StructGet (type_idx s x, i, op)
  | StructSet (x, op) -> StructSet (type_idx s x, op)
  | ArrayNew (x, op) -> ArrayNew (type_idx s x, op)
  | ArrayNewFixed (x, n) -> ArrayNewFixed (type_idx s x, n)
  | ArrayNewElem (x, y) -> ArrayNewElem (type_idx s x, elem_idx s y)
  | ArrayNewData (x, y) -> ArrayNewData (type_idx s x, data_idx s y)
  | ArrayGet (x, op) -> ArrayGet (type_idx s x, op)
  | ArraySet x -> ArraySet (type_idx s x)
  | ArrayLen -> ArrayLen
  | ArrayFill x -> ArrayFill (type_idx s x)
  | ArrayCopy (x, y) -> ArrayCopy (type_idx s x, type_idx s y)
  | ArrayInitElem (x, y) -> ArrayInitElem (type_idx s x, elem_idx s y)
  | ArrayInitData (x, y) -> ArrayInitData (type_idx s x, data_idx s y)
  | ExternConvert op -> ExternConvert op
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
  | Br x -> Br (label_idx s x)
  | BrIf x -> BrIf (label_idx s x)
  | BrOnNull x -> BrOnNull (label_idx s x)
  | BrOnNonNull x -> BrOnNonNull (label_idx s x)
  | BrOnCast (x, rt1, rt2) -> BrOnCast (label_idx s x, ref_type s rt1, ref_type s rt2)
  | BrOnCastFail (x, rt1, rt2) -> BrOnCastFail (label_idx s x, ref_type s rt1, ref_type s rt2)
  | BrTable (xs, x) -> BrTable (list label_idx s xs, label_idx s x)
  | Return -> Return
  | Call x -> Call (func_idx s x)
  | CallRef x -> CallRef (type_idx s x)
  | CallIndirect (x, y) -> CallIndirect (table_idx s x, type_idx s y)
  | ReturnCall x -> ReturnCall (type_idx s x)
  | ReturnCallRef x -> ReturnCallRef (type_idx s x)
  | ReturnCallIndirect (x, y) -> ReturnCallIndirect (table_idx s x, type_idx s y)
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

let table s (t : table) = {t.it with ttype = table_type s t.it.ttype} @@ t.at
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

let start s (f : start) = {sfunc = func_idx s f.it.sfunc} @@ f.at

let type_ s (t : type_) = rec_type s t.it @@ t.at

let module_ s (m : module_) =
  { types = list type_ s m.it.types;
    globals = list global s m.it.globals;
    tables = list table s m.it.tables;
    memories = list memory s m.it.memories;
    funcs = list func s m.it.funcs;
    start = opt start s m.it.start;
    elems = list elem s m.it.elems;
    datas = list data s m.it.datas;
    imports = list import s m.it.imports;
    exports = list export s m.it.exports;
  } @@ m.at
