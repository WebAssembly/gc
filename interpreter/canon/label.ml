(* Type Graph Representation: Labels *)

module T = Types

type t = string

let dummy = ""


(* Inspection *)

let is_struct label = label.[0] = '\x01'
let is_array label = label.[0] = '\x02'
let is_func label = label.[0] = '\x03'


(* Extract labels from types *)

type context =
  { scc : IntSet.t;
    buf : Buffer.t;
    mutable edges : int list;  (* negative when internal edge *)
  }

let bool b x = Buffer.add_uint8 b (if x then 1 else 0)
let rec int b i =
  if 0 <= i && i < 128 then Buffer.add_uint8 b i else
  (Buffer.add_uint8 b (i land 0x7f lor 0x80); int b (i lsr 7))

let rec def_label c = function
  | T.StructDefType (T.StructType fts) ->
    Buffer.add_uint8 c.buf 1;
    List.iter (field_label c) fts;
    Buffer.add_uint8 c.buf 0
  | T.ArrayDefType (T.ArrayType ft) ->
    Buffer.add_uint8 c.buf 2;
    field_label c ft
  | T.FuncDefType (T.FuncType (vts1, vts2)) ->
    Buffer.add_uint8 c.buf 3;
    List.iter (value_label c) vts1;
    Buffer.add_uint8 c.buf 0;
    List.iter (value_label c) vts2;
    Buffer.add_uint8 c.buf 0

and field_label c (T.FieldType (st, mut)) =
  match st with
  | T.ValueStorageType vt ->
    value_label c vt;
    bool c.buf (mut = T.Mutable)
  | T.PackedStorageType sz ->
    Buffer.add_uint8 c.buf (0xf8 lor T.packed_size sz);
    bool c.buf (mut = T.Mutable)

and value_label c = function
  | T.NumType t -> Buffer.add_uint8 c.buf (num_label t)
  | T.RefType (null, ht) ->
    Buffer.add_uint8 c.buf (ref_label ht);
    heap_label c ht;
    bool c.buf (null = T.Nullable)
  | T.BotType -> assert false

and num_label = function
  | T.I32Type -> 1
  | T.I64Type -> 2
  | T.F32Type -> 3
  | T.F64Type -> 4

and ref_label = function
  | T.AnyHeapType -> 10
  | T.EqHeapType -> 11
  | T.I31HeapType -> 12
  | T.DataHeapType -> 13
  | T.FuncHeapType -> 14
  | T.ExternHeapType -> 15
  | T.DefHeapType _ -> 16
  | T.RttHeapType _ -> 17
  | T.BotHeapType -> assert false

and heap_label c = function
  | T.DefHeapType x -> var_label c x
  | T.RttHeapType (x, d) ->
    var_label c x; int c.buf (Int32.to_int (Option.value d ~default:(-1l)) + 1)
  | _ -> ()

and var_label c = function
  | T.SynVar x' ->
    let x = Int32.to_int x' in
    let id = if IntSet.mem x c.scc then (-x-1) else x in
    c.edges <- id :: c.edges
  | T.SemVar _ -> assert false
