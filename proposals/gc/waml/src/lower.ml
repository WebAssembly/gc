open Emit

module T = Type
module W = Emit.W
module E = Env


(* Locations *)

type null = Null | Nonull

type loc =
  | PreLoc of int32
  | LocalLoc of int32
  | GlobalLoc of int32
  | ClosureLoc of null * int32 * int32 * int32 (* fldidx, localidx, typeidx *)

type func_loc = {funcidx : int32; typeidx : int32; arity : int}

let as_local_loc = function LocalLoc idx -> idx | _ -> assert false
let as_global_loc = function GlobalLoc idx -> idx | _ -> assert false


(* Representations *)

type rep =
  | DropRep                (* value never used *)
  | BlockRep of null       (* like Boxed, but empty tuples are suppressed *)
  | BoxedRep of null       (* concrete boxed representation *)
  | BoxedAbsRep of null    (* abstract boxed representation *)
  | UnboxedRep of null     (* representation with unboxed type or concrete ref types *)
  | UnboxedLaxRep of null  (* like Unboxed, but Int may have junk high bit *)

let null_rep = function
  | BlockRep n | BoxedRep n | BoxedAbsRep n | UnboxedRep n | UnboxedLaxRep n -> n
  | DropRep -> assert false

(* Configurable *)
let boxed_if flag null = if !flag then BoxedRep null else UnboxedRep null
let local_rep () = boxed_if Flags.box_locals Null    (* values stored in locals *)
let clos_rep () = boxed_if Flags.box_locals Nonull   (* values stored in closures *)
let global_rep () = boxed_if Flags.box_globals Null  (* values stored in globals *)
let struct_rep () = boxed_if Flags.box_modules Nonull (* values stored in structs *)
let tmp_rep () = boxed_if Flags.box_temps Null       (* values stored in temps *)
let pat_rep () = boxed_if Flags.box_scrut Nonull     (* values fed into patterns *)

(* Non-configurable *)
let ref_rep = BoxedAbsRep Null      (* expecting a reference *)
let rigid_rep = UnboxedRep Nonull   (* values produced or to be consumed *)
let lax_rep = UnboxedLaxRep Nonull  (* lax ints produced or consumed *)
let field_rep = BoxedAbsRep Nonull  (* values stored in fields *)
let arg_rep = BoxedAbsRep Nonull    (* argument and result values *)
let unit_rep = BlockRep Nonull      (* nothing on stack *)

let loc_rep = function
  | PreLoc _ -> rigid_rep
  | GlobalLoc _ -> global_rep ()
  | LocalLoc _ -> local_rep ()
  | ClosureLoc _ -> clos_rep ()


let max_func_arity = if !Flags.headless then 4 else 12

let clos_arity_idx = 0l
let clos_code_idx = 1l
let clos_env_idx = 2l  (* first environment entry *)


(* Environment *)

type data_con = {tag : int32; typeidx : int32; arity : int}
type data = (string * data_con) list
type env = (loc * func_loc option, data, loc * func_loc option, unit) E.env
type scope = PreScope | LocalScope | GlobalScope

let make_env () =
  let env = ref E.empty in
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region)
      (PreLoc (Int32.of_int i), None)
  ) Prelude.vals;
  env

let scope_rep = function
  | PreScope -> rigid_rep
  | LocalScope -> local_rep ()
  | GlobalScope -> global_rep ()


(* Compilation context *)

module ClosKey =
struct
  type t = W.value_type list * W.value_type list * W.field_type list
  let compare = compare
end

module ClosMap = Map.Make(ClosKey)
module IdxMap = Map.Make(Int32)

type clos_idxs = {codeidx : int32; closidx : int32; envidx : int32}
type ctxt_ext =
  { envs : (scope * env ref) list;
    clostypes : clos_idxs ClosMap.t ref;
    rttglobals : int32 IdxMap.t ref;
    texts : int32 Env.Map.t ref;
    data : int32 ref;
  }
type ctxt = ctxt_ext Emit.ctxt

let make_ext_ctxt () : ctxt_ext =
  { envs = [(PreScope, make_env ())];
    clostypes = ref ClosMap.empty;
    rttglobals = ref IdxMap.empty;
    texts = ref Env.Map.empty;
    data = ref (-1l);
  }
let make_ctxt () : ctxt = Emit.make_ctxt (make_ext_ctxt ())

let enter_scope ctxt scope : ctxt =
  {ctxt with ext = {ctxt.ext with envs = (scope, ref E.empty) :: ctxt.ext.envs}}

let current_scope ctxt : scope * env ref =
  List.hd ctxt.ext.envs


(* Lowering types *)

let lower_ref null ht =
  match null with
  | Null -> W.(ref_null_heap ht)
  | Nonull -> W.(ref_heap ht)

let abs = W.eq
let absref = lower_ref Nonull abs

let rec lower_value_type ctxt at rep t : W.value_type =
  match T.norm t, rep with
  | t, (BlockRep n | BoxedRep n)
  | (T.Data _ as t), BoxedAbsRep n -> lower_ref n (lower_heap_type ctxt at t)
  | _, BoxedAbsRep n -> lower_ref n abs
  | (T.Bool | T.Byte | T.Int), _ -> W.i32
  | T.Float, _ -> W.f64
  | t, (UnboxedRep n | UnboxedLaxRep n) -> lower_ref n (lower_heap_type ctxt at t)
  | _, DropRep -> assert false

and lower_heap_type ctxt at t : W.heap_type =
  match T.norm t with
  | T.Var _ -> W.eq
  | T.Bool | T.Byte | T.Int -> W.i31
  | T.Tup [] -> W.eq
  | T.Data t1 ->
    (match T.as_fun_flat t1 with
    | [], _ -> W.i31
    | ts, _ -> W.rtt (lower_con_type ctxt at ts)
    )
  | t -> W.(type_ (lower_var_type ctxt at t))

and lower_anycon_type ctxt at : int32 =
  emit_type ctxt at W.(sub [] (struct_ [field i32]))

and lower_con_type ctxt at ts : int32 =
  if ts = [] then -1l else
  let anycon = lower_anycon_type ctxt at in
  let vts = List.map (lower_value_type ctxt at field_rep) ts in
  let fts = List.map W.field vts in
  emit_type ctxt at W.(sub [anycon] (struct_ (field i32 :: fts)))

and lower_var_type ctxt at t : int32 =
  match T.norm t with
  | T.Float ->
    emit_type ctxt at W.(sub [] (struct_ [field f64]))
  | T.Text ->
    emit_type ctxt at W.(sub [] (array (field_mut_pack i8)))
  | T.Tup ts ->
    let ts = List.map (lower_value_type ctxt at field_rep) ts in
    emit_type ctxt at W.(sub [] (struct_ (List.map W.field ts)))
  | T.Ref t1 ->
    let t1' = lower_value_type ctxt at field_rep t1 in
    emit_type ctxt at W.(sub [] (struct_ [field_mut t1']))
  | T.Fun (_, _, arity_opt) ->
    (match !arity_opt with
    | T.KnownArity arity -> snd (lower_func_type ctxt at arity)
    | T.UnknownArity | T.VariableArity -> lower_anyclos_type ctxt at
    )
  | T.Pack s -> snd (lower_sig_type ctxt at s)
  | _ -> Printf.printf "%s\n%!" (T.string_of_typ t); assert false

and lower_anyclos_type ctxt at : int32 =
  emit_type ctxt at W.(sub [] (struct_ [field i32]))

and lower_func_type ctxt at arity : int32 * int32 =
  let argts, _ = lower_param_types ctxt at arity in
  let key = (argts, [absref], []) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; _} -> codeidx, closidx
  | None ->
    let anyclos = lower_anyclos_type ctxt at in
    let code, def_code = emit_type_deferred ctxt at in
    let closdt = W.(sub [anyclos] (struct_ [field i32; field (ref_ code)])) in
    let clos = emit_type ctxt at closdt in
    let codedt = W.(sub [] (func (ref_ clos :: argts) [absref])) in
    def_code codedt;
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos

and lower_clos_type ctxt at arity flds : int32 * int32 * int32 =
  let argts, _ = lower_param_types ctxt at arity in
  let key = (argts, [absref], flds) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; envidx} -> codeidx, closidx, envidx
  | None ->
    let code, clos = lower_func_type ctxt at arity in
    let envdt =
      W.(sub [clos] (struct_ (field i32 :: field (ref_ code) :: flds))) in
    let clos_env = emit_type ctxt at envdt in
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos_env} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos, clos_env

and lower_param_types ctxt at arity : W.value_type list * int32 option =
  if arity <= max_func_arity then
    List.init arity (fun _ -> absref), None
  else
    let argv = emit_type ctxt at W.(sub [] (array (field_mut absref))) in
    W.[ref_ argv], Some argv

and lower_block_type ctxt at rep t : W.block_type =
  match t, rep with
  | _, DropRep
  | T.Tup [], BlockRep _ -> W.void
  | t, _ -> W.result (lower_value_type ctxt at rep t)


(* Lowering signatures *)

and lower_sig_type ctxt at s : W.value_type * int32 =
  match s with
  | T.Str (_, str) -> lower_str_type ctxt at str
  | T.Fct (_, s1, s2) ->
    let _, clos = lower_fct_type ctxt at s1 s2 in
    W.ref_ clos, clos

and lower_str_type ctxt at str : W.value_type * int32 =
  let mod_ts = List.map (fun (_, s) ->
    fst (lower_sig_type ctxt at s.Source.it)) (E.mods str) in
  let val_ts = List.map (fun (_, pt) ->
    lower_value_type ctxt at (struct_rep ()) (T.as_mono pt.Source.it)) (E.vals str) in
  let x = emit_type ctxt at W.(sub [] (struct_ (List.map field (mod_ts @ val_ts)))) in
  W.ref_ x, x

and lower_fct_type ctxt at s1 s2 : int32 * int32 =
  let t1, _ = lower_sig_type ctxt at s1 in
  let t2, _ = lower_sig_type ctxt at s2 in
  let key = ([t1], [t2], []) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; _} -> codeidx, closidx
  | None ->
    let code, def_code = emit_type_deferred ctxt at in
    let closdt = W.(sub [] (struct_ [field i32; field (ref_ code)])) in
    let clos = emit_type ctxt at closdt in
    let codedt = W.(sub [] (func [ref_ clos; t1] [t2])) in
    def_code codedt;
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos

let lower_fct_clos_type ctxt at s1 s2 flds : int32 * int32 * int32 =
  let t1, _ = lower_sig_type ctxt at s1 in
  let t2, _ = lower_sig_type ctxt at s2 in
  let key = ([t1], [t2], flds) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; envidx} -> codeidx, closidx, envidx
  | None ->
    let code, clos = lower_fct_type ctxt at s1 s2 in
    let envdt =
      W.(sub [clos] (struct_ (field i32 :: field (ref_ code) :: flds))) in
    let clos_env = emit_type ctxt at envdt in
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos_env} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos, clos_env


(* Closure environments *)

let lower_clos_env ctxt at vars rec_xs
  : W.field_type list * (string * T.typ * int) list =
  let open Syntax in
  let fixups = ref [] in
  let k = E.Map.cardinal vars.mods in
  let flds =
    List.mapi (fun i (x, s) ->
      W.field (fst (lower_sig_type ctxt at s))
    ) (Vars.bindings vars.mods)
    @
    List.mapi (fun i (x, t) ->
      if E.Set.mem x rec_xs then begin
        fixups := (x, t, i + k) :: !fixups;
        W.field_mut (lower_value_type ctxt at (local_rep ()) t)
      end else
        W.field (lower_value_type ctxt at (clos_rep ()) t)
    ) (Vars.bindings vars.vals)
  in flds, !fixups


(* RTTs *)

let lower_rtt_global ctxt xat typeidx : int32 =
  match IdxMap.find_opt typeidx !(ctxt.ext.rttglobals) with
  | Some idx -> idx
  | None ->
    let open W.Source in
    let const = W.[rtt_canon (typeidx @@ xat) @@ xat] @@ xat in
    let t = W.(rttref typeidx) in
    let idx = emit_global ctxt xat W.Immutable t (Some const) in
    ctxt.ext.rttglobals := IdxMap.add typeidx idx !(ctxt.ext.rttglobals);
    idx
