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
  | SynVar x -> SynVar (lookup s x)
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
  | Select tso -> Select (opt (list value_type) s tso)
  | RefNull t -> RefNull (heap_type s t)
  | StructNew (x, op) -> StructNew (type_idx s x, op)
  | StructGet (x, i, op) -> StructGet (type_idx s x, i, op)
  | StructSet (x, op) -> StructSet (type_idx s x, op)
  | ArrayNew (x, op) -> ArrayNew (type_idx s x, op)
  | ArrayGet (x, op) -> ArrayGet (type_idx s x, op)
  | ArraySet x -> ArraySet (type_idx s x)
  | RttCanon x -> RttCanon (type_idx s x)
  | Block (bt, es) -> Block (block_type s bt, block s es)
  | Loop (bt, es) -> Loop (block_type s bt, block s es)
  | If (bt, es1, es2) -> If (block_type s bt, block s es1, block s es2)
  | Let (bt, ls, es) -> Let (block_type s bt, list local s ls, block s es)
  | CallIndirect (x, y) -> CallIndirect (x, type_idx s y)
  | FuncBind x -> FuncBind (type_idx s x)
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

let table s (t : table) = {ttype = table_type s t.it.ttype} @@ t.at
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

let type_ s (t : type_) = def_type s t.it @@ t.at

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
