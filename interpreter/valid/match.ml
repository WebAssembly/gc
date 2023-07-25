open Types


(* Context *)

type context = def_type list

let lookup c x = Lib.List32.nth c x


(* Extremas *)

let abs_of_str_type _c = function
  | DefStructT _ | DefArrayT _ -> StructHT
  | DefFuncT _ -> FuncHT

let rec top_of_str_type c st =
  top_of_heap_type c (abs_of_str_type c st)

and top_of_heap_type c = function
  | AnyHT | NoneHT | EqHT | StructHT | ArrayHT | I31HT -> AnyHT
  | FuncHT | NoFuncHT -> FuncHT
  | ExternHT | NoExternHT -> ExternHT
  | DefHT dt -> top_of_str_type c (expand_def_type dt)
  | VarHT (StatX x) -> top_of_str_type c (expand_def_type (lookup c x))
  | VarHT (RecX _) | BotHT -> assert false

let rec bot_of_str_type c st =
  bot_of_heap_type c (abs_of_str_type c st)

and bot_of_heap_type c = function
  | AnyHT | NoneHT | EqHT | StructHT | ArrayHT | I31HT -> NoneHT
  | FuncHT | NoFuncHT -> NoFuncHT
  | ExternHT | NoExternHT -> NoExternHT
  | DefHT dt -> bot_of_str_type c (expand_def_type dt)
  | VarHT (StatX x) -> bot_of_str_type c (expand_def_type (lookup c x))
  | VarHT (RecX _) | BotHT -> assert false


(* Subtyping *)

let match_null _c nul1 nul2 =
  match nul1, nul2 with
  | NoNull, Null -> true
  | _, _ -> nul1 = nul2

let match_limits _c lim1 lim2 =
  I32.ge_u lim1.min lim2.min &&
  match lim1.max, lim2.max with
  | _, None -> true
  | None, Some _ -> false
  | Some i, Some j -> I32.le_u i j


let match_num_type _c t1 t2 =
  t1 = t2

let match_vec_type _c t1 t2 =
  t1 = t2

let rec match_heap_type c t1 t2 =
  match t1, t2 with
  | AnyHT, AnyHT -> true
  | EqHT, AnyHT -> true
  | StructHT, AnyHT -> true
  | ArrayHT, AnyHT -> true
  | I31HT, AnyHT -> true
  | I31HT, EqHT -> true
  | StructHT, EqHT -> true
  | ArrayHT, EqHT -> true
  | ExternHT, ExternHT -> true
  | NoneHT, t -> match_heap_type c t AnyHT
  | NoFuncHT, t -> match_heap_type c t FuncHT
  | NoExternHT, t -> match_heap_type c t ExternHT
  | VarHT (StatX x1), _ -> match_heap_type c (DefHT (lookup c x1)) t2
  | _, VarHT (StatX x2) -> match_heap_type c t1 (DefHT (lookup c x2))
  | DefHT dt1, DefHT dt2 -> match_def_type c dt1 dt2
  | DefHT dt, t ->
    (match expand_def_type dt, t with
    | DefStructT _, AnyHT -> true
    | DefStructT _, EqHT -> true
    | DefStructT _, StructHT -> true
    | DefArrayT _, AnyHT -> true
    | DefArrayT _, EqHT -> true
    | DefArrayT _, ArrayHT -> true
    | DefFuncT _, FuncHT -> true
    | _ -> false
    )
  | BotHT, _ -> true
  | _, _ -> t1 = t2

and match_ref_type c t1 t2 =
  match t1, t2 with
  | (nul1, t1'), (nul2, t2') ->
    match_null c nul1 nul2 && match_heap_type c t1' t2'

and match_val_type c t1 t2 =
  match t1, t2 with
  | NumT t1', NumT t2' -> match_num_type c t1' t2'
  | VecT t1', VecT t2' -> match_vec_type c t1' t2'
  | RefT t1', RefT t2' -> match_ref_type c t1' t2'
  | BotT, _ -> true
  | _, _ -> false

and match_result_type c ts1 ts2 =
  List.length ts1 = List.length ts2 &&
  List.for_all2 (match_val_type c) ts1 ts2


and match_pack_type _c t1 t2 =
  t1 = t2

and match_storage_type c st1 st2 =
  match st1, st2 with
  | ValStorageT t1, ValStorageT t2 -> match_val_type c t1 t2
  | PackStorageT t1, PackStorageT t2 -> match_pack_type c t1 t2
  | _, _ -> false

and match_field_type c (FieldT (mut1, st1)) (FieldT (mut2, st2)) =
  mut1 = mut2 && match_storage_type c st1 st2 &&
  match mut1 with
  | Cons -> true
  | Var -> match_storage_type c st2 st1


and match_struct_type c (StructT fts1) (StructT fts2) =
  List.length fts1 >= List.length fts2 &&
  List.for_all2 (match_field_type c) (Lib.List.take (List.length fts2) fts1) fts2

and match_array_type c (ArrayT ft1) (ArrayT ft2) =
  match_field_type c ft1 ft2

and match_func_type c (FuncT (ts11, ts12)) (FuncT (ts21, ts22)) =
  match_result_type c ts21 ts11 && match_result_type c ts12 ts22


and match_str_type c dt1 dt2 =
  match dt1, dt2 with
  | DefStructT st1, DefStructT st2 -> match_struct_type c st1 st2
  | DefArrayT at1, DefArrayT at2 -> match_array_type c at1 at2
  | DefFuncT ft1, DefFuncT ft2 -> match_func_type c ft1 ft2
  | _, _ -> false

and match_def_type c dt1 dt2 =
  dt1 == dt2 ||  (* optimisation *)
  let s = subst_of c in subst_def_type s dt1 = subst_def_type s dt2 ||
  let SubT (_fin, hts1, _st) = unroll_def_type dt1 in
  List.exists (fun ht1 -> match_heap_type c ht1 (DefHT dt2)) hts1


let match_global_type c (GlobalT (mut1, t1)) (GlobalT (mut2, t2)) =
  mut1 = mut2 && match_val_type c t1 t2 &&
  match mut1 with
  | Cons -> true
  | Var -> match_val_type c t2 t1

let match_table_type c (TableT (lim1, t1)) (TableT (lim2, t2)) =
  match_limits c lim1 lim2 && match_ref_type c t1 t2 && match_ref_type c t2 t1

let match_memory_type c (MemoryT lim1) (MemoryT lim2) =
  match_limits c lim1 lim2


let match_extern_type c et1 et2 =
  match et1, et2 with
  | ExternFuncT dt1, ExternFuncT dt2 -> match_def_type c dt1 dt2
  | ExternTableT tt1, ExternTableT tt2 -> match_table_type c tt1 tt2
  | ExternMemoryT mt1, ExternMemoryT mt2 -> match_memory_type c mt1 mt2
  | ExternGlobalT gt1, ExternGlobalT gt2 -> match_global_type c gt1 gt2
  | _, _ -> false
