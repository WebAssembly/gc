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

let loc_rep = function
  | PreLoc _ -> UnboxedRigidRep
  | GlobalLoc _ | LocalLoc _ | ClosureLoc _ -> BoxedRep

let is_boxed_rep = function
  | BlockRep | BoxedRep -> true
  | _ -> false

let max_func_arity = 5

let clos_arity_idx = 0l
let clos_code_idx = 1l
let clos_env_idx = 2l  (* first environment entry *)


(* Lowering types *)

let rec lower_value_type ctxt at rep t : W.value_type =
  if is_boxed_rep rep then W.(RefType (Nullable, EqHeapType)) else
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
  let codedt = W.(type_func (ref_ clos :: argts) [eqref]) in
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
    List.init arity (fun _ -> W.eqref), None
  else
    let argv = emit_type ctxt at W.(type_array (field_mut eqref)) in
    W.[ref_ argv], Some argv

and lower_block_type ctxt at rep t : W.block_type =
  match t with
  | T.Tup [] when rep = BlockRep -> W.void
  | t -> W.result (lower_value_type ctxt at rep t)
