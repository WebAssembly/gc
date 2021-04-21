open Emit

module T = Type
module W = Emit.W


(* Locations *)

type loc =
  | PreLoc of int32
  | LocalLoc of int32
  | GlobalLoc of int32
  | ClosureLoc of int32 * int32 * int32 (* fldidx, localidx, typeidx *)

type func_loc = {funcidx : int32; arity : int}


(* Representations *)

type rep =
  | DropRep         (* value never used *)
  | BlockRep        (* like Boxed, but empty tuples are suppressed *)
  | BoxedRep        (* representation that is compatible with anyref *)
  | UnboxedLaxRep   (* like UnboxedRigid, but Int may have junk high bit *)
  | UnboxedRigidRep (* representation with unboxed type or concrete ref types *)

(* TODO: used UnboxedRigid for locals, closures, patterns *)
let pat_rep = BoxedRep
let local_rep = BoxedRep
let global_rep = BoxedRep
let struct_rep = BoxedRep

let loc_rep = function
  | PreLoc _ -> UnboxedRigidRep
  | GlobalLoc _ -> global_rep
  | LocalLoc _ | ClosureLoc _ -> local_rep

let is_boxed_rep = function
  | BlockRep | BoxedRep -> true
  | _ -> false

let as_local_loc = function LocalLoc idx -> idx | _ -> assert false
let as_global_loc = function GlobalLoc idx -> idx | _ -> assert false

let max_func_arity = 5

let clos_arity_idx = 0l
let clos_code_idx = 1l
let clos_env_idx = 2l  (* first environment entry *)


(* Lowering types *)

let boxed = W.eq
let boxedref = W.(ref_null_heap boxed)

let rec lower_value_type ctxt at rep t : W.value_type =
  if is_boxed_rep rep then boxedref else
  match T.norm t with
  | T.Bool | T.Byte | T.Int -> W.i32
  | T.Float -> W.f64
  | t -> W.(ref_null_heap (lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match T.norm t with
  | T.Var _ -> W.eq
  | T.Bool | T.Byte | T.Int -> W.i31
  | T.Tup [] -> W.eq
  | t -> W.(type_ (lower_var_type ctxt at t))

and lower_var_type ctxt at t : int32 =
  match T.norm t with
  | T.Float ->
    emit_type ctxt at W.(type_struct [field f64])
  | T.Text ->
    emit_type ctxt at W.(type_array (field_mut_pack i8))
  | T.Tup ts ->
    let ts = List.map (lower_value_type ctxt at BoxedRep) ts in
    emit_type ctxt at W.(type_struct (List.map W.field ts))
  | T.Ref t1 ->
    let t1' = lower_value_type ctxt at BoxedRep t1 in
    emit_type ctxt at W.(type_struct [field_mut t1'])
  | T.Fun _ ->
    lower_anyclos_type ctxt at
  | _ -> Printf.printf "%s\n%!" (T.string_of_typ t); assert false

and lower_anyclos_type ctxt at : int32 =
  emit_type ctxt at W.(type_struct [field i32])

and lower_func_type ctxt at arity : int32 * int32 =
  let code, def_code = emit_type_deferred ctxt at in
  let closdt = W.(type_struct [field i32; field (ref_ code)]) in
  let clos = emit_type ctxt at closdt in
  let argts, _ = lower_param_types ctxt at arity in
  let codedt = W.(type_func (ref_ clos :: argts) [boxedref]) in
  def_code codedt;
  code, clos

and lower_clos_type ctxt at arity envts : int32 * int32 * int32 =
  let code, clos = lower_func_type ctxt at arity in
  let closdt =
    W.(type_struct (field i32 :: field (ref_ code) :: List.map field envts)) in
  let clos_env = emit_type ctxt at closdt in
  code, clos, clos_env

and lower_param_types ctxt at arity : W.value_type list * int32 option =
  if arity <= max_func_arity then
    List.init arity (fun _ -> boxedref), None
  else
    let argv = emit_type ctxt at W.(type_array (field_mut boxedref)) in
    W.[ref_ argv], Some argv

and lower_block_type ctxt at rep t : W.block_type =
  match t, rep with
  | _, DropRep -> W.void
  | T.Tup [], BlockRep -> W.void
  | t, _ -> W.result (lower_value_type ctxt at rep t)

let lower_con_type ctxt at ts : W.value_type * int32 =
  if ts = [] then
    W.i31ref, -1l
  else begin
    let vts = List.map (lower_value_type ctxt at UnboxedRigidRep) ts in
    let fts = List.map W.field vts in
    let con = emit_type ctxt at W.(type_struct (field i32 :: fts)) in
    W.(ref_null_heap (rtt_n con 1l)), con
  end

let lower_val_type ctxt at rep t x : W.value_type =
  if x.[0] = Char.lowercase_ascii x.[0] then
    lower_value_type ctxt at global_rep t
  else
    fst (lower_con_type ctxt at (fst (T.as_fun_flat t)))


(* Lowering signatures *)

let rec lower_sig_type ctxt at s : W.value_type * int32 =
  match s with
  | T.Str (_, str) -> lower_str_type ctxt at str
  | T.Fct (_, s1, s2) ->
    let _, clos = lower_fct_type ctxt at s1 s2 in
    W.ref_ clos, clos

and lower_str_type ctxt at str : W.value_type * int32 =
  let mod_ts = List.map (fun (_, s) ->
    fst (lower_sig_type ctxt at s.Source.it)) (Env.mods str) in
  let val_ts = List.map (fun (x, pt) ->
    lower_val_type ctxt at struct_rep (T.as_mono pt.Source.it) x) (Env.vals str) in
  let x = emit_type ctxt at W.(type_struct (List.map field (mod_ts @ val_ts))) in
  W.ref_ x, x

and lower_fct_type ctxt at s1 s2 : int32 * int32 =
  let t1, _ = lower_sig_type ctxt at s1 in
  let t2, _ = lower_sig_type ctxt at s2 in
  let code, def_code = emit_type_deferred ctxt at in
  let closdt = W.(type_struct [field i32; field (ref_ code)]) in
  let clos = emit_type ctxt at closdt in
  let codedt = W.(type_func [ref_ clos; t1] [t2]) in
  def_code codedt;
  code, clos

let lower_fct_clos_type ctxt at s1 s2 envts : int32 * int32 * int32 =
  let code, clos = lower_fct_type ctxt at s1 s2 in
  let closdt =
    W.(type_struct (field i32 :: field (ref_ code) :: List.map field envts)) in
  let clos_env = emit_type ctxt at closdt in
  code, clos, clos_env


(* Closure environments *)

let lower_clos_env ctxt at vars : W.value_type list =
  let open Syntax in
  List.map (fun (_, s) ->
      fst (lower_sig_type ctxt at s)
    ) (Vars.bindings vars.mods)
  @
  List.map (fun (x, t) ->
      lower_val_type ctxt at struct_rep t x
    ) (Vars.bindings vars.vals)
