open Wasm
open Source
open Ast
open Types

module Map = Map.Make(Int32)

type t = int32 Map.t


(* Constructors *)

let empty : t = Map.empty

let add_type s x y = Map.add x y s

let union (s1 : t) (s2 : t) : t = Map.union (fun _ _ _ -> assert false) s1 s2


(* Apply *)

let lookup s x =
  match Map.find_opt x s with
  | Some x' -> x'
  | None -> x

let type_idx s x = lookup s x.it @@ x.at

let opt subst s xo = Option.map (subst s) xo
let list subst s xs = List.map (subst s) xs

let var_type s = function
  | StatX x -> StatX (lookup s x)
  | _ -> assert false

let num_type s = function
  | (I32T | I64T | F32T | F64T) as t -> t

let vec_type s = function
  | V128T as t -> t

let rec heap_type s = function
  | AnyHT | EqHT | I31HT | StructHT | ArrayHT | NoneHT
  | FuncHT | NoFuncHT | ExternHT | NoExternHT | BotHT as t -> t
  | VarHT x -> VarHT (var_type s x)
  | DefHT dt -> DefHT (def_type s dt)

and ref_type s = function
  | (nul, t) -> (nul, heap_type s t)

and val_type s = function
  | NumT t -> NumT (num_type s t)
  | VecT t -> VecT (vec_type s t)
  | RefT t -> RefT (ref_type s t)
  | BotT -> BotT

and packed_type s t = t

and storage_type s = function
  | ValStorageT t -> ValStorageT (val_type s t)
  | PackStorageT t -> PackStorageT (packed_type s t)

and field_type s (FieldT (mut, st)) = FieldT (mut, storage_type s st)

and struct_type s (StructT fts) = StructT (list field_type s fts)
and array_type s (ArrayT ft) = ArrayT (field_type s ft)
and func_type s (FuncT (ts1, ts2)) =
  FuncT (list val_type s ts1, list val_type s ts2)

and str_type s = function
  | DefStructT st -> DefStructT (struct_type s st)
  | DefArrayT at -> DefArrayT (array_type s at)
  | DefFuncT ft -> DefFuncT (func_type s ft)

and sub_type s = function
  | SubT (fin, hts, st) -> SubT (fin, List.map (heap_type s) hts, str_type s st)

and rec_type s = function
  | RecT sts -> RecT (List.map (sub_type s) sts)

and def_type s = function
  | DefT (rt, i) -> DefT (rec_type s rt, i)

let global_type s (GlobalT (mut, t)) = GlobalT (mut, val_type s t)
let table_type s (TableT (lim, t)) = TableT (lim, ref_type s t)
let memory_type s (MemoryT lim) = MemoryT lim

let block_type s = function
  | VarBlockType x -> VarBlockType (type_idx s x)
  | ValBlockType t -> ValBlockType (opt val_type s t)

let local s (l : local) = {ltype = val_type s l.it.ltype} @@ l.at

let rec instr s (e : instr) = instr' s e.it @@ e.at
and instr' s = function
  | Select tso -> Select (opt (list val_type) s tso)
  | RefNull t -> RefNull (heap_type s t)
  | RefTest rt -> RefTest (ref_type s rt)
  | RefCast rt -> RefCast (ref_type s rt)
  | StructNew (x, op) -> StructNew (type_idx s x, op)
  | StructGet (x, i, op) -> StructGet (type_idx s x, i, op)
  | StructSet (x, op) -> StructSet (type_idx s x, op)
  | ArrayNew (x, op) -> ArrayNew (type_idx s x, op)
  | ArrayNewFixed (x, n) -> ArrayNewFixed (type_idx s x, n)
  | ArrayNewElem (x, y) -> ArrayNewElem (type_idx s x, y)
  | ArrayNewData (x, y) -> ArrayNewData (type_idx s x, y)
  | ArrayGet (x, op) -> ArrayGet (type_idx s x, op)
  | ArraySet x -> ArraySet (type_idx s x)
  | ArrayFill x -> ArrayFill (type_idx s x)
  | ArrayCopy (x, y) -> ArrayCopy (type_idx s x, type_idx s y)
  | ArrayInitElem (x, y) -> ArrayInitElem (type_idx s x, y)
  | ArrayInitData (x, y) -> ArrayInitData (type_idx s x, y)
  | Block (bt, es) -> Block (block_type s bt, block s es)
  | Loop (bt, es) -> Loop (block_type s bt, block s es)
  | If (bt, es1, es2) -> If (block_type s bt, block s es1, block s es2)
  | BrOnCast (x, rt1, rt2) -> BrOnCast (x, ref_type s rt1, ref_type s rt2)
  | BrOnCastFail (x, rt1, rt2) -> BrOnCastFail (x, ref_type s rt1, ref_type s rt2)
  | CallRef x -> CallRef (type_idx s x)
  | CallIndirect (x, y) -> CallIndirect (x, type_idx s y)
  | ReturnCall x -> ReturnCall (type_idx s x)
  | ReturnCallRef x -> ReturnCallRef (type_idx s x)
  | ReturnCallIndirect (x, y) -> ReturnCallIndirect (x, type_idx s y)
  | instr' -> instr'

and block s (es : instr list) =
  list instr s es

let const s (c : const) =
  block s c.it @@ c.at

let global s (g : global) =
  { gtype = global_type s g.it.gtype;
    ginit = const s g.it.ginit;
  } @@ g.at

let func s (f : func) =
  { ftype = type_idx s f.it.ftype;
    locals = list local s f.it.locals;
    body = block s f.it.body;
  } @@ f.at

let table s (t : table) =
    {ttype = table_type s t.it.ttype; tinit = const s t.it.tinit} @@ t.at
let memory s (m : memory) = {mtype = memory_type s m.it.mtype} @@ m.at

let segment_mode s (m : segment_mode) =
  match m.it with
  | Passive -> Passive @@ m.at
  | Declarative -> Declarative @@ m.at
  | Active {index; offset} -> Active {index; offset = const s offset} @@ m.at

let elem s (e : elem_segment) =
  { etype = ref_type s e.it.etype;
    einit = list const s e.it.einit;
    emode = segment_mode s e.it.emode;
  } @@ e.at

let data s (d : data_segment) =
  { dinit = d.it.dinit;
    dmode = segment_mode s d.it.dmode;
  } @@ d.at

let import_desc s (d : import_desc) =
  match d.it with
  | FuncImport x -> FuncImport (type_idx s x) @@ d.at
  | TableImport tt -> TableImport (table_type s tt) @@ d.at
  | MemoryImport mt -> MemoryImport (memory_type s mt) @@ d.at
  | GlobalImport gt -> GlobalImport (global_type s gt) @@ d.at

let export s (e : export) = e

let import s (i : import) =
  { module_name = i.it.module_name;
    item_name = i.it.item_name;
    idesc = import_desc s i.it.idesc;
  } @@ i.at

let type_ s (t : type_) = rec_type s t.it @@ t.at

let module_ s (m : module_) =
  { types = list type_ s m.it.types;
    globals = list global s m.it.globals;
    tables = list table s m.it.tables;
    memories = list memory s m.it.memories;
    funcs = list func s m.it.funcs;
    start = m.it.start;
    elems = list elem s m.it.elems;
    datas = list data s m.it.datas;
    imports = list import s m.it.imports;
    exports = list export s m.it.exports;
  } @@ m.at
