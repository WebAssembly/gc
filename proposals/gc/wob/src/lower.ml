open Source
open Emit

module T = Type
module E = Env
module W = Emit.W


(* Failure *)

exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Helpers *)

let int32 = W.I32.of_int_s
let (+%) = Int32.add
let (-%) = Int32.sub


(* Environment *)

type loc = DirectLoc of int32 | InstanceLoc of string
type env = (T.sort * loc, T.sort * loc) E.env
type scope =
  PreScope | GlobalScope | BlockScope | FuncScope | ClassScope of T.typ

let as_direct_loc = function
  | DirectLoc i -> i
  | _ -> assert false

let hidden_prefix = "hidden-"
let hidden_length = String.length hidden_prefix
let hidden i = hidden_prefix ^ Int32.to_string i
let is_hidden x = x > hidden_prefix && x < "hidden."
let as_hidden x =
  let s = String.sub x hidden_length (String.length x - hidden_length) in
  Int32.of_string s

let cls_disp = 0l
let cls_rtt = 1l
let cls_new = 2l
let cls_pre_alloc = 3l
let cls_post_alloc = 4l
let cls_sup = 5l


let make_env () =
  let env = ref Env.empty in
  List.iteri (fun i (y, _) ->
    env := E.extend_typ !env Source.(y @@ Prelude.region) (T.LetS, DirectLoc (int32 i))
  ) Prelude.typs;
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region) (T.LetS, DirectLoc (int32 i))
  ) Prelude.vals;
  env

type pass = FullPass | FuncPass | LetPass | VarPass


(* Class table *)

module ClsEnv = Map.Make(Int)

type cls_def =
  { env : env;
    inst_flds : W.field_type list;
    disp_flds : W.field_type list;
    param_vals : W.val_type list;
    pre_vals : (string * W.val_type) list;
    overrides : (int32 * (string * W.func_type)) list;
    mutable new_fidx : int32;
    mutable pre_alloc_fidx : int32;
    mutable post_alloc_fidx : int32;
  }

type cls =
  { sup : cls option;
    inst_tidx : int32;
    disp_tidx : int32;
    cls_tidx : int32;
    mutable new_tidx : int32;
    mutable pre_tidx : int32;
    mutable post_tidx : int32;
    mutable def : cls_def lazy_t;
  }

type cls_env = cls ClsEnv.t

let make_cls sup inst_tidx disp_tidx cls_tidx =
  { sup;
    inst_tidx;
    disp_tidx;
    cls_tidx;
    new_tidx = -1l;
    pre_tidx = -1l;
    post_tidx = -1l;
    def = lazy (failwith "make_cls");
  }

let make_cls_def () =
  { env = E.empty;
    inst_flds = [];
    disp_flds = [];
    param_vals = [];
    pre_vals = [];
    overrides = [];
    new_fidx = -1l;
    pre_alloc_fidx = -1l;
    post_alloc_fidx = -1l;
  }

let cls_first_inst_idx cls =
  match cls.sup with
  | None -> 1
  | Some sup ->
    let lazy sup_def = sup.def in
    1 + List.length sup_def.inst_flds

let _cls_first_disp_idx cls =
  match cls.sup with
  | None -> 0
  | Some sup ->
    let lazy sup_def = sup.def in
    List.length sup_def.disp_flds


(* Compilation context *)

module FuncEnv = Map.Make(Int32)

type ctxt = ctxt_ext Emit.ctxt
and func_env = (ctxt -> W.val_type list -> W.val_type list -> (ctxt -> int32 -> unit) -> unit) FuncEnv.t
and ctxt_ext =
  { envs : (scope * env ref) list;
    clss : cls_env ref;
    funcs : func_env ref;
    texts : int32 Env.Map.t ref;
    data : int32 ref;
    self : string;
    tcls : T.cls option;
    ret : T.typ;
  }

let make_ext_ctxt () : ctxt_ext =
  { envs = [(PreScope, make_env ())];
    clss = ref ClsEnv.empty;
    funcs = ref FuncEnv.empty;
    texts = ref Env.Map.empty;
    data = ref (-1l);
    self = "";
    tcls = None;
    ret = T.Tup [];
  }

let make_ctxt () : ctxt =
  Emit.make_ctxt (make_ext_ctxt ())

let enter_scope ctxt scope : ctxt =
  {ctxt with ext = {ctxt.ext with envs = (scope, ref E.empty) :: ctxt.ext.envs}}

let current_scope ctxt : scope * env ref =
  List.hd ctxt.ext.envs


let emit_cls ctxt at id sup :
    cls * (W.sub_type -> W.sub_type -> W.sub_type -> int32 -> int32 -> int32 -> unit) =
  let inst_tidx, f1 = emit_type_deferred ctxt at in
  let disp_tidx, f2 = emit_type_deferred ctxt at in
  let cls_tidx, f3 = emit_type_deferred ctxt at in
  let cls = make_cls sup inst_tidx disp_tidx cls_tidx in
  ctxt.ext.clss := ClsEnv.add id cls !(ctxt.ext.clss);
  cls,
  fun t1 t2 t3 x4 x5 x6 ->
    f1 t1; f2 t2; f3 t3;
    cls.new_tidx <- x4; cls.pre_tidx <- x5; cls.post_tidx <- x6

let shift_loc k = function
  | (T.LetS | T.VarS) as s, DirectLoc i -> s, DirectLoc (i +% k)
  | s, l -> s, l

let rec ctxt_flush ctxt =
  let triggered = ref false in
  ClsEnv.iter (fun _ cls ->
    if not (Lazy.is_val cls.def) then begin
      ignore (Lazy.force cls.def);
      triggered := true
    end
  ) !(ctxt.ext.clss);
  if !triggered then ctxt_flush ctxt


(* Type lowering *)

let lower_val_rtt ctxt at : W.val_type =
  W.(RefT (NoNull, EqHT))

let lower_var_rtt ctxt at : int32 =
  let rtt_vt = W.(RefT (Null, EqHT)) in
  let rtt_ft = W.(FieldT (Var, ValStorageT rtt_vt)) in
  emit_type ctxt at W.(sub_final [] (array rtt_ft))

let rec lower_val_type ctxt at t : W.val_type =
  match t with
  | T.Bool | T.Byte | T.Int -> W.(NumT I32T)
  | T.Float -> W.(NumT F64T)
  | t -> W.(RefT (Null, lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match t with
  | T.Var _ | T.Null | T.Tup [] | T.Bot -> W.EqHT
  | T.Box (T.Bool | T.Byte) -> W.I31HT
  | t -> W.(VarHT (StatX (lower_var_type ctxt at t)))

and lower_obj_type ctxt at : int32 * int32 =
  let disp_idx = emit_type ctxt at W.(sub [] (struct_ [])) in
  let disp_vt = W.(RefT (NoNull, VarHT (StatX disp_idx))) in
  let disp_ft = W.(FieldT (Cons, ValStorageT disp_vt)) in
  emit_type ctxt at W.(sub [] (struct_ [disp_ft])), disp_idx

and lower_var_type ctxt at t : int32 =
  match t with
  | T.Obj -> fst (lower_obj_type ctxt at)
  | T.Inst (tcls, _ts) ->
    (lower_class ctxt at tcls).inst_tidx
  | T.Text ->
    let ft = W.(FieldT (Var, PackStorageT Pack.Pack8)) in
    emit_type ctxt at W.(sub_final [] (array ft))
  | T.Box t1 ->
    let ft = lower_field_type ctxt at W.Cons t1 in
    emit_type ctxt at W.(sub_final [] (struct_ [ft]))
  | T.Tup ts ->
    let fts = List.map (lower_field_type ctxt at W.Cons) ts in
    emit_type ctxt at W.(sub_final [] (struct_ fts))
  | T.Array (t1, _m) ->
    let ft = lower_field_type ctxt at W.Var t1 in
    emit_type ctxt at W.(sub_final [] (array ft))
  | T.Func _ -> nyi at "function types"
  | T.Class tcls -> (lower_class ctxt at tcls).cls_tidx
  | _ -> assert false

and lower_storage_type ctxt at t : W.storage_type =
  match t with
  | T.Bool | T.Byte -> W.(PackStorageT Pack.Pack8)
  | T.Int | T.Float -> W.(ValStorageT (lower_val_type ctxt at t))
  | t -> W.(ValStorageT (RefT (Null, EqHT)))

and lower_field_type ctxt at mut t : W.field_type =
  W.(FieldT (mut, lower_storage_type ctxt at t))

and lower_block_val_type ctxt at t : W.val_type option =
  match t with
  | T.Tup [] -> None
  | t -> Some (lower_val_type ctxt at t)

and lower_block_type ctxt at t : W.block_type =
  W.ValBlockType (lower_block_val_type ctxt at t)

and lower_block_type_func ctxt at ts1 ts2 : W.block_type =
  let ts1' = List.map (lower_val_type ctxt at) ts1 in
  let ts2' = List.map (lower_val_type ctxt at) ts2 in
  let idx = emit_type ctxt at W.(sub_final [] (func ts1' ts2')) in
  W.(VarBlockType (Source.(@@) idx at))

and lower_stack_type ctxt at t : W.val_type list =
  Option.to_list (lower_block_val_type ctxt at t)

and lower_func_type ctxt at t : W.func_type =
  let rtt_t = lower_val_rtt ctxt at in
  match t with
  | T.Func (ys, ts1, t2) ->
    W.FuncT (
      (if !Flags.parametric then [] else List.map (fun _ -> rtt_t) ys) @
      List.map (lower_val_type ctxt at) ts1,
      lower_stack_type ctxt at t2
    )
  | T.Class tcls ->
    W.FuncT (
      (if !Flags.parametric then [] else List.map (fun _ -> rtt_t) tcls.T.tparams) @
      List.map (lower_val_type ctxt at) tcls.T.vparams,
      [lower_val_type ctxt at (T.Inst (tcls, List.map T.var tcls.T.tparams))]
    )
  | _ -> assert false

and lower_class ctxt at tcls =
  match ClsEnv.find_opt tcls.T.id !(ctxt.ext.clss) with Some cls -> cls | None ->

  let (cls, define_cls), sup, tsup_def =
    match tcls.T.sup with
    | T.Obj ->
      let sup_inst, sup_disp = lower_obj_type ctxt at in
      let sup_dummy = make_cls None sup_inst sup_disp (-1l) in
      sup_dummy.def <- lazy (make_cls_def ());
      emit_cls ctxt at tcls.T.id None, sup_dummy, []
    | T.Inst (tsup, _) ->
      let sup = lower_class ctxt at tsup in
      emit_cls ctxt at tcls.T.id (Some sup), sup, tsup.T.def
    | _ -> assert false
  in

  cls.def <- lazy (
    let inst_t = T.Inst (tcls, List.map T.var tcls.T.tparams) in
    let inst_vt = lower_val_type ctxt at inst_t in

    let lazy sup_def = sup.def in
    let offset = if !Flags.parametric then 0 else List.length tcls.T.tparams in
    let start = int32 (List.length sup_def.inst_flds + 1) in
    let param_tbinds =
      if !Flags.parametric then [] else
      List.mapi (fun i _ ->
        hidden (int32 i +% start), lower_val_rtt ctxt at
      ) tcls.T.tparams
    in
    let param_vbinds =
      List.mapi (fun i t ->
        hidden (int32 (i + offset) +% start), lower_val_type ctxt at t
      ) tcls.T.vparams
    in
    let param_binds = param_tbinds @ param_vbinds in
    let param_vts = List.map snd param_binds in
    let param_fts =
      List.map (fun vtI -> W.(FieldT (Cons, ValStorageT vtI)))
        param_vts
    in

    let clsenv, pre_binds_r, overrides, inst_fts_r, disp_fts_r, _, _ =
      List.fold_left
      (fun (clsenv, pre_binds, ov, inst_fts, disp_fts, inst_i, disp_i) (x, (s, t)) ->
        match E.find_opt_val Source.(x @@ no_region) sup_def.env with
        | Some sl ->
          let i = as_direct_loc (snd sl.it) in
          let ft_idx = lookup_ref_field_type ctxt sup.disp_tidx i in
          clsenv, pre_binds, (i, (x, lookup_func_type ctxt ft_idx))::ov,
          inst_fts, disp_fts, inst_i, disp_i
        | None ->
        match s with
        | T.LetS ->
          let ft = lower_field_type ctxt at W.Cons t in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc inst_i),
          (x, lower_val_type ctxt at t) :: pre_binds, ov,
          ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
        | T.VarS ->
          let ft = lower_field_type ctxt at W.Var t in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc inst_i),
          (hidden (-1l), lower_val_type ctxt at t) :: pre_binds, ov,
          ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
        | T.FuncS ->
          let ys, ts1, t2 = T.as_func t in
          let W.FuncT (ts1', ts2') =
            lower_func_type ctxt at (T.Func (ys, ts1, t2)) in
          let ts1'' = lower_val_type ctxt at inst_t :: ts1' in
          let idx = emit_type ctxt at W.(sub_final [] (func ts1'' ts2')) in
          let dt = W.(VarHT (StatX idx)) in
          let st = W.(ValStorageT (RefT (NoNull, dt))) in
          let ft = W.(FieldT (Cons, st)) in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc disp_i),
          pre_binds, ov,
          inst_fts, ft::disp_fts, inst_i, disp_i +% 1l
        | T.ClassS -> nyi at "nested class definitions"
        | T.ProhibitedS -> assert false
      ) (sup_def.env, [], [], [], [],
          int32 (1 + offset + List.length tcls.T.vparams +
            List.length sup_def.inst_flds),
          int32 (List.length sup_def.disp_flds))
        (W.Lib.List.drop (List.length tsup_def) tcls.T.def)
    in

    let ty_vt = W.(RefT (Null, EqHT)) in
    let ty_ft = W.(FieldT (Var, ValStorageT ty_vt)) in
    let ty_fts = if !Flags.parametric then [] else [ty_ft] in
    let pre_binds = sup_def.pre_vals @ param_binds @ List.rev pre_binds_r in
    let inst_fts = sup_def.inst_flds @ param_fts @ List.rev inst_fts_r in
    let disp_fts = sup_def.disp_flds @ List.rev disp_fts_r @ ty_fts in
    let disp_vt = W.(RefT (NoNull, VarHT (StatX cls.disp_tidx))) in
    let disp_ft = W.(FieldT (Cons, ValStorageT disp_vt)) in
(* RTTs
    let rtt_ht = W.(RttHT (StatX cls.inst_tidx)) in
    let rtt_vt = W.(RefT (NoNull, rtt_ht)) in
*)
    let rtt_vt = W.(RefT (Null, NoneHT)) in
    let rtt_ft = W.(FieldT (Cons, ValStorageT rtt_vt)) in
    let new_fnt = lower_func_type ctxt at (T.Class tcls) in
    let new_idx = emit_type ctxt at W.(sub_final [] (DefFuncT new_fnt)) in
    let new_vt = W.(RefT (NoNull, VarHT (StatX new_idx))) in
    let new_ft = W.(FieldT (Cons, ValStorageT new_vt)) in
    let pre_fnt = W.(FuncT (param_vts, List.map snd pre_binds)) in
    let pre_idx = emit_type ctxt at W.(sub_final [] (DefFuncT pre_fnt)) in
    let pre_vt = W.(RefT (NoNull, VarHT (StatX pre_idx))) in
    let pre_ft = W.(FieldT (Cons, ValStorageT pre_vt)) in
    let post_fnt = W.(FuncT ([inst_vt], [])) in
    let post_idx = emit_type ctxt at W.(sub_final [] (DefFuncT post_fnt)) in
    let post_vt = W.(RefT (NoNull, VarHT (StatX post_idx))) in
    let post_ft = W.(FieldT (Cons, ValStorageT post_vt)) in
    let sup_vt = if cls.sup = None then W.i32 else
      W.(RefT (NoNull, VarHT (StatX sup.cls_tidx))) in
    let sup_ft = W.(FieldT (Cons, ValStorageT sup_vt)) in
    let cls_fts = [disp_ft; rtt_ft; new_ft; pre_ft; post_ft; sup_ft] in
    let inst_st = W.(sub [sup.inst_tidx] (struct_ (disp_ft :: inst_fts))) in
    let disp_st = W.(sub [sup.disp_tidx] (struct_ disp_fts)) in
    let cls_st = W.(sub_final [] (struct_ cls_fts)) in
    let clsenv' =
      if !Flags.parametric then clsenv else
      List.fold_left (fun clsenv (x, _) ->
        E.extend_typ clsenv (Source.(@@) x at) (T.LetS, DirectLoc (as_hidden x))
      ) clsenv param_tbinds
    in
    let clsenv'' =
      List.fold_left (fun clsenv (x, _) ->
        E.extend_val clsenv (Source.(@@) x at) (T.LetS, DirectLoc (as_hidden x))
      ) clsenv' param_vbinds
    in
    define_cls inst_st disp_st cls_st new_idx pre_idx post_idx;
    { (make_cls_def ()) with
      env = clsenv'';
      inst_flds = inst_fts;
      disp_flds = disp_fts;
      param_vals = param_vts;
      pre_vals = pre_binds;
      overrides = overrides;
    }
  );
  cls
