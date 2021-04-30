(* Super-inefficient hash table over types, just for verification purposes *)

module T = Types

module Hash =
struct
  type t = T.def_type

  let context : Match.context ref = ref [||]

  let equal dt1 dt2 = Match.eq_def_type !context [] dt1 dt2

  let rec hash_list hash = function
    | [] -> 0
    | x::xs -> hash x lxor (hash_list hash xs lsl 1)

  let rec hash = function
    | T.StructDefType (T.StructType fts) -> 1 + hash_list hash_field fts
    | T.ArrayDefType (T.ArrayType ft) -> 2 + hash_field ft
    | T.FuncDefType (T.FuncType (ts1, ts2)) ->
      3 + hash_list hash_val ts1 lxor hash_list hash_val ts2

  and hash_field (T.FieldType (st, _)) = hash_storage st

  and hash_storage = function
    | T.ValueStorageType t -> hash_val t
    | T.PackedStorageType sz -> T.packed_size sz

  and hash_val = function
    | T.NumType t -> Hashtbl.hash t
    | T.RefType (_, ht) -> hash_heap ht
    | T.BotType -> assert false

  and hash_heap = function
    | T.DefHeapType _ -> 37
    | T.RttHeapType _ -> 62
    | ht -> Hashtbl.hash ht
end

include Hashtbl.Make(Hash)
