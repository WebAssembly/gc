open Source
open Syntax
open Emit

module T = Type
module E = Env
module W = Emit.W


(* Failure *)

exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Helpers *)

let type_of = Source.et
let result_type_of d = fst (type_of d)
let bind_type_of d = snd (type_of d)

let (@@) = W.Source.(@@)

let i32 = W.I32.of_int_s
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
    env := E.extend_typ !env Source.(y @@ Prelude.region) (T.LetS, DirectLoc (i32 i))
  ) Prelude.typs;
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region) (T.LetS, DirectLoc (i32 i))
  ) Prelude.vals;
  env

type pass = FullPass | FuncPass | LetPass | VarPass


(* Class table *)

module ClsEnv = Map.Make(Int)

type cls_def =
  { env : env;
    inst_flds : W.field_type list;
    disp_flds : W.field_type list;
    param_vals : W.value_type list;
    pre_vals : (string * W.value_type) list;
    overrides : (int32 * (string * W.func_type)) list;
    mutable new_idx : int32;
    mutable pre_alloc_idx : int32;
    mutable post_alloc_idx : int32;
  }

type cls =
  { sup : cls option;
    inst_idx : int32;
    disp_idx : int32;
    cls_idx : int32;
    mutable def : cls_def lazy_t;
  }

type cls_env = cls ClsEnv.t

let make_cls sup inst_idx disp_idx cls_idx =
  { sup;
    inst_idx;
    disp_idx;
    cls_idx;
    def = lazy (failwith "make_cls");
  }

let make_cls_def () =
  { env = E.empty;
    inst_flds = [];
    disp_flds = [];
    param_vals = [];
    pre_vals = [];
    overrides = [];
    new_idx = -1l;
    pre_alloc_idx = -1l;
    post_alloc_idx = -1l;
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
and func_env = (ctxt -> W.value_type list -> W.value_type list -> (ctxt -> int32 -> unit) -> unit) FuncEnv.t
and ctxt_ext =
  { envs : (scope * env ref) list;
    clss : cls_env ref;
    funcs : func_env ref;
    self : string;
    tcls : T.cls option;
    ret : T.typ;
  }

let make_ext_ctxt () : ctxt_ext =
  { envs = [(PreScope, make_env ())];
    clss = ref ClsEnv.empty;
    funcs = ref FuncEnv.empty;
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
    cls * (W.def_type -> W.def_type -> W.def_type -> unit) =
  let inst_idx, f1 = emit_type_deferred ctxt at in
  let disp_idx, f2 = emit_type_deferred ctxt at in
  let cls_idx, f3 = emit_type_deferred ctxt at in
  let cls = make_cls sup inst_idx disp_idx cls_idx in
  ctxt.ext.clss := ClsEnv.add id cls !(ctxt.ext.clss);
  cls, fun t1 t2 t3 -> f1 t1; f2 t2; f3 t3

let shift_loc k = function
  | (T.LetS | T.VarS) as s, DirectLoc i -> s, DirectLoc (i +% k)
  | s, l -> s, l

let emit_let ctxt at bt ts f =
  Emit.emit_let ctxt at bt ts (fun ctxt' ->
    let _, env = current_scope ctxt' in
    let shift = i32 (List.length ts) in
    env := E.map_vals (shift_loc shift) !env;
    f ctxt';
    (* Unshift -- can't just restore, since there might be new locals *)
    env := E.map_vals (shift_loc (0l -% shift)) !env;
  )


(* Debug printing *)

let string_of_sort = function
  | T.LetS -> "let"
  | T.VarS -> "var"
  | T.FuncS -> "func"
  | T.ClassS -> "class"
  | T.ProhibitedS -> "prohibited"

let string_of_loc = function
  | DirectLoc i -> Int32.to_string i
  | InstanceLoc x -> "." ^ x

let print_env env =
  E.iter_typs (fun x sl -> let s, l = sl.it in
    Printf.printf " type %s(%s)=%s" (string_of_sort s) x (string_of_loc l)) env;
  E.iter_vals (fun x sl -> let s, l = sl.it in
    Printf.printf " %s(%s)=%s" (string_of_sort s) x (string_of_loc l)) env;
  Printf.printf "\n"

let string_of_type ctxt idx =
  match Emit.lookup_def_type_opt ctxt idx with
  | Some dt -> W.string_of_def_type dt
  | None -> "?"

let string_of_field_type ctxt idx i =
  if Emit.lookup_def_type_opt ctxt idx = None then "?" else
  let idx' = Emit.lookup_ref_field_type ctxt idx i in
  Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'

let rec _print_cls ctxt cls =
  let open Printf in
  printf "inst_idx = %ld = %!%s\n" cls.inst_idx (string_of_type ctxt cls.inst_idx);
  printf "disp_idx = %ld = %s\n" cls.disp_idx (string_of_type ctxt cls.disp_idx);
  printf "cls_idx = %ld = %s\n" cls.cls_idx (string_of_type ctxt cls.cls_idx);
  printf "new : %s\n" (string_of_field_type ctxt cls.cls_idx cls_new);
  printf "pre : %s\n" (string_of_field_type ctxt cls.cls_idx cls_pre_alloc);
  printf "post : %s\n" (string_of_field_type ctxt cls.cls_idx cls_post_alloc);
  if not (Lazy.is_val cls.def) then printf "(under definition)\n" else begin
    let lazy def = cls.def in
    printf "inst_flds =";
      List.iter (printf " %s") (List.map W.string_of_field_type def.inst_flds);
      printf "\n";
    printf "disp_flds =";
      List.iter (printf " %s") (List.map W.string_of_field_type def.disp_flds);
      printf "\n";
    printf "param_vals =";
      List.iter (printf " %s") (List.map W.string_of_value_type def.param_vals);
      printf "\n";
    printf "pre_vals =";
      List.iter (fun (x, t) ->
        printf " %s:%s" x (W.string_of_value_type t)) def.pre_vals;
      printf "\n";
    printf "overrides =";
      List.iter (fun (i, (x, ft)) ->
        printf " %s/%ld:%s" x i (W.string_of_func_type ft)
      ) def.overrides;
      printf "\n";
    printf "env ="; print_env def.env
  end;
  if cls.sup = None then printf "sup = none\n%!" else printf "sup =\n";
  Option.iter (_print_cls ctxt) cls.sup


(* Lowering types *)

let lower_value_rtt ctxt at : W.value_type =
  W.(RefType (NonNullable, EqHeapType))

let lower_var_rtt ctxt at : int32 =
  let rtt_vt = W.(RefType (Nullable, EqHeapType)) in
  let rtt_ft = W.(FieldType (ValueStorageType rtt_vt, Mutable)) in
  emit_type ctxt at W.(ArrayDefType (ArrayType rtt_ft))

let rec lower_value_type ctxt at t : W.value_type =
  match t with
  | T.Bool | T.Byte | T.Int -> W.(NumType I32Type)
  | T.Float -> W.(NumType F64Type)
  | t -> W.(RefType (Nullable, lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match t with
  | T.Var _ | T.Null | T.Tup [] | T.Bot -> W.EqHeapType
  | T.Box (T.Bool | T.Byte) -> W.I31HeapType
  | t -> W.(DefHeapType (SynVar (lower_var_type ctxt at t)))

and lower_var_type ctxt at t : int32 =
  match t with
  | T.Obj ->
    let disp_idx = emit_type ctxt at W.(StructDefType (StructType [])) in
    let disp_vt = W.(RefType (NonNullable, DefHeapType (SynVar disp_idx))) in
    let disp_ft = W.(FieldType (ValueStorageType disp_vt, Immutable)) in
    emit_type ctxt at W.(StructDefType (StructType [disp_ft]))
  | T.Inst (tcls, _ts) ->
    (lower_class ctxt at tcls).inst_idx
  | T.Text ->
    let ft = W.(FieldType (PackedStorageType Pack8, Mutable)) in
    emit_type ctxt at W.(ArrayDefType (ArrayType ft))
  | T.Box t1 ->
    let ft = lower_field_type ctxt at W.Immutable t1 in
    emit_type ctxt at W.(StructDefType (StructType [ft]))
  | T.Tup ts ->
    let fts = List.map (lower_field_type ctxt at W.Immutable) ts in
    emit_type ctxt at W.(StructDefType (StructType fts))
  | T.Array t1 ->
    let ft = lower_field_type ctxt at W.Mutable t1 in
    emit_type ctxt at W.(ArrayDefType (ArrayType ft))
  | T.Func _ -> nyi at "function types"
  | T.Class tcls -> (lower_class ctxt at tcls).cls_idx
  | _ -> assert false

and lower_storage_type ctxt at t : W.storage_type =
  match t with
  | T.Bool | T.Byte -> W.(PackedStorageType Pack8)
  | T.Int | T.Float -> W.(ValueStorageType (lower_value_type ctxt at t))
  | t -> W.(ValueStorageType (RefType (Nullable, EqHeapType)))

and lower_field_type ctxt at mut t : W.field_type =
  W.(FieldType (lower_storage_type ctxt at t, mut))

and lower_block_value_type ctxt at t : W.value_type option =
  match t with
  | T.Tup [] -> None
  | t -> Some (lower_value_type ctxt at t)

and lower_block_type ctxt at t : W.block_type =
  W.ValBlockType (lower_block_value_type ctxt at t)

and lower_block_type_func ctxt at ts1 ts2 : W.block_type =
  let ts1' = List.map (lower_value_type ctxt at) ts1 in
  let ts2' = List.map (lower_value_type ctxt at) ts2 in
  W.(VarBlockType (SynVar
    (emit_type ctxt at (FuncDefType (FuncType (ts1', ts2'))))))

and lower_stack_type ctxt at t : W.value_type list =
  Option.to_list (lower_block_value_type ctxt at t)

and lower_func_type ctxt at t : W.func_type =
  let rtt_t = lower_value_rtt ctxt at in
  match t with
  | T.Func (ys, ts1, t2) ->
    W.FuncType (
      (if !Flags.parametric then [] else List.map (fun _ -> rtt_t) ys) @
      List.map (lower_value_type ctxt at) ts1,
      lower_stack_type ctxt at t2
    )
  | T.Class tcls ->
    W.FuncType (
      (if !Flags.parametric then [] else List.map (fun _ -> rtt_t) tcls.T.tparams) @
      List.map (lower_value_type ctxt at) tcls.T.vparams,
      [lower_value_type ctxt at (T.Inst (tcls, List.map T.var tcls.T.tparams))]
    )
  | _ -> assert false

and lower_class ctxt at tcls =
  match ClsEnv.find_opt tcls.T.id !(ctxt.ext.clss) with Some cls -> cls | None ->

  let (cls, define_cls), sup, tsup_def =
    match tcls.T.sup with
    | T.Obj ->
      let sup_dummy = make_cls None (-1l) (-1l) (-1l) in
      sup_dummy.def <- lazy (make_cls_def ());
      emit_cls ctxt at tcls.T.id None, sup_dummy, []
    | T.Inst (tsup, _) ->
      let sup = lower_class ctxt at tsup in
      emit_cls ctxt at tcls.T.id (Some sup), sup, tsup.T.def
    | _ -> assert false
  in

  cls.def <- lazy (
    let inst_t = T.Inst (tcls, List.map T.var tcls.T.tparams) in
    let inst_vt = lower_value_type ctxt at inst_t in

    let lazy sup_def = sup.def in
    let offset = if !Flags.parametric then 0 else List.length tcls.T.tparams in
    let start = i32 (List.length sup_def.inst_flds + 1) in
    let param_tbinds =
      if !Flags.parametric then [] else
      List.mapi (fun i _ ->
        hidden (i32 i +% start), lower_value_rtt ctxt at
      ) tcls.T.tparams
    in
    let param_vbinds =
      List.mapi (fun i t ->
        hidden (i32 (i + offset) +% start), lower_value_type ctxt at t
      ) tcls.T.vparams
    in
    let param_binds = param_tbinds @ param_vbinds in
    let param_vts = List.map snd param_binds in
    let param_fts =
      List.map (fun vtI -> W.(FieldType (ValueStorageType vtI, Immutable)))
        param_vts
    in

    let clsenv, pre_binds_r, overrides, inst_fts_r, disp_fts_r, _, _ =
      List.fold_left
      (fun (clsenv, pre_binds, ov, inst_fts, disp_fts, inst_i, disp_i) (x, (s, t)) ->
        match E.find_opt_val Source.(x @@ no_region) sup_def.env with
        | Some sl ->
          let i = as_direct_loc (snd sl.it) in
          let ft_idx = lookup_ref_field_type ctxt sup.disp_idx i in
          clsenv, pre_binds, (i, (x, lookup_func_type ctxt ft_idx))::ov,
          inst_fts, disp_fts, inst_i, disp_i
        | None ->
        match s with
        | T.LetS ->
          let ft = lower_field_type ctxt at W.Immutable t in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc inst_i),
          (x, lower_value_type ctxt at t) :: pre_binds, ov,
          ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
        | T.VarS ->
          let ft = lower_field_type ctxt at W.Mutable t in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc inst_i),
          (hidden (-1l), lower_value_type ctxt at t) :: pre_binds, ov,
          ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
        | T.FuncS ->
          let ys, ts1, t2 = T.as_func t in
          let W.FuncType (ts1', ts2') =
            lower_func_type ctxt at (T.Func (ys, ts1, t2)) in
          let fnt = W.FuncType (lower_value_type ctxt at inst_t :: ts1', ts2') in
          let idx = emit_type ctxt at W.(FuncDefType (fnt)) in
          let dt = W.(DefHeapType (SynVar idx)) in
          let st = W.(ValueStorageType (RefType (NonNullable, dt))) in
          let ft = W.(FieldType (st, Immutable)) in
          E.extend_val clsenv (Source.(@@) x at) (s, DirectLoc disp_i),
          pre_binds, ov,
          inst_fts, ft::disp_fts, inst_i, disp_i +% 1l
        | T.ClassS -> nyi at "nested class definitions"
        | T.ProhibitedS -> assert false
      ) (sup_def.env, [], [], [], [],
          i32 (1 + offset + List.length tcls.T.vparams +
            List.length sup_def.inst_flds),
          i32 (List.length sup_def.disp_flds))
        (W.Lib.List.drop (List.length tsup_def) tcls.T.def)
    in

    let ty_vt = W.(RefType (Nullable, EqHeapType)) in
    let ty_ft = W.(FieldType (ValueStorageType ty_vt, Mutable)) in
    let ty_fts = if !Flags.parametric then [] else [ty_ft] in
    let pre_binds = sup_def.pre_vals @ param_binds @ List.rev pre_binds_r in
    let inst_fts = sup_def.inst_flds @ param_fts @ List.rev inst_fts_r in
    let disp_fts = sup_def.disp_flds @ List.rev disp_fts_r @ ty_fts in
    let disp_vt = W.(RefType (NonNullable, DefHeapType (SynVar cls.disp_idx))) in
    let disp_ft = W.(FieldType (ValueStorageType disp_vt, Immutable)) in
    let rtt_ht = W.(RttHeapType (SynVar cls.inst_idx,
      Some (i32 (T.cls_depth tcls)))) in
    let rtt_vt = W.(RefType (NonNullable, rtt_ht)) in
    let rtt_ft = W.(FieldType (ValueStorageType rtt_vt, Immutable)) in
    let new_fnt = lower_func_type ctxt at (T.Class tcls) in
    let new_idx = emit_type ctxt at W.(FuncDefType (new_fnt)) in
    let new_vt = W.(RefType (NonNullable, DefHeapType (SynVar new_idx))) in
    let new_ft = W.(FieldType (ValueStorageType new_vt, Immutable)) in
    let pre_fnt = W.(FuncType (param_vts, List.map snd pre_binds)) in
    let pre_idx = emit_type ctxt at W.(FuncDefType pre_fnt) in
    let pre_vt = W.(RefType (NonNullable, DefHeapType (SynVar pre_idx))) in
    let pre_ft = W.(FieldType (ValueStorageType pre_vt, Immutable)) in
    let post_fnt = W.(FuncType ([inst_vt], [])) in
    let post_idx = emit_type ctxt at W.(FuncDefType post_fnt) in
    let post_vt = W.(RefType (NonNullable, DefHeapType (SynVar post_idx))) in
    let post_ft = W.(FieldType (ValueStorageType post_vt, Immutable)) in
    let sup_vt = if cls.sup = None then W.i32t else
      W.(RefType (NonNullable, DefHeapType (SynVar sup.cls_idx))) in
    let sup_ft = W.(FieldType (ValueStorageType sup_vt, Immutable)) in
    let cls_fts = [disp_ft; rtt_ft; new_ft; pre_ft; post_ft; sup_ft] in
    let inst_dt = W.(StructDefType (StructType (disp_ft :: inst_fts))) in
    let disp_dt = W.(StructDefType (StructType disp_fts)) in
    let cls_dt = W.(StructDefType (StructType cls_fts)) in
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
    define_cls inst_dt disp_dt cls_dt;
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


(* Coercions *)

let default_exp ctxt at t : W.instr' list =
  let instr' =
    match t with
    | T.Bool | T.Byte | T.Int -> W.i32_const (0l @@ at)
    | T.Float -> W.f64_const (W.F64.of_float 0.0 @@ at)
    | T.Var _ | T.Null | T.Text | T.Obj | T.Boxed | T.Box _ | T.Tup _
    | T.Inst _ | T.Array _ | T.Func _ | T.Class _ | T.Bot ->
      W.ref_null (lower_heap_type ctxt at t)
  in [instr']

let default_const ctxt at t : W.const =
  List.map (fun instr' -> instr' @@ at) (default_exp ctxt at t) @@ at

let compile_coerce_block_type ctxt at t =
  match t with
  | T.Tup [] -> emit_instr ctxt at W.(drop)
  | _ -> ()

let compile_coerce_value_type ctxt at t =
  match t with
  | T.Tup [] ->
    emit_instr ctxt at (W.ref_null (lower_heap_type ctxt at (T.Tup [])))
  | _ -> ()

let compile_coerce_abs_value_type ctxt at t =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match t with
  | T.Null | T.Bot | T.Tup [] ->
    emit ctxt W.[drop; ref_null (lower_heap_type ctxt at t)]
  | T.Box (T.Bool | T.Byte) ->
    emit ctxt W.[ref_as_i31]
  | T.Text | T.Box _ | T.Tup _ | T.Obj
  | T.Inst _ | T.Array _ | T.Func _ | T.Class _ ->
    let t' = lower_value_type ctxt at t in
    let tmpidx = emit_local ctxt at W.(RefType (Nullable, EqHeapType)) in
    let typeidx = lower_var_type ctxt at t in
    emit ctxt W.[
      local_tee (tmpidx @@ at);
      ref_is_null;
      if_ (valbt t') [
        ref_null (DefHeapType (SynVar typeidx)) @@ at
      ] (
        [ local_get (tmpidx @@ at) @@ at;
          ref_as_data @@ at;
        ] @
        (match t with
        | T.Inst (tcls, _) ->
          let rec sub tcls =
            let cls = lower_class ctxt at tcls in
            (match T.sup_cls tcls with
            | None -> [rtt_canon (lower_var_type ctxt at T.Obj @@ at) @@ at]
            | Some tsup -> sub tsup
            ) @ [rtt_sub (cls.inst_idx @@ at) @@ at]
          in sub tcls
        | _ -> [rtt_canon (typeidx @@ at) @@ at]
        ) @
        [ ref_cast @@ at;
        ]
      )
    ]
  | _ -> ()

let compile_coerce_abs_block_type ctxt at t =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match t with
  | T.Tup [] -> emit ctxt W.[drop]
  | _ -> compile_coerce_abs_value_type ctxt at t


let compile_coerce_null_type ctxt at t1 t2 =
  if t1 = T.Null && t2 <> T.Null then
  List.iter (emit_instr ctxt at) W.[
    drop;
    ref_null (lower_heap_type ctxt at t2);
  ]


(* Variables *)

let rec find_var find_opt ctxt x envs : scope * T.sort * loc =
  match envs with
  | [] ->
    Printf.printf "[find_var `%s` @@ %s]\n%!" x.it (Source.string_of_region x.at);
    assert false
  | (scope, env)::envs' ->
    match find_opt x !env with
    | None ->
      let (scope', _, _) as result = find_var find_opt ctxt x envs' in
      (match scope', scope with
      | (PreScope | GlobalScope), _
      | (FuncScope | BlockScope), BlockScope
      | ClassScope _, (FuncScope | BlockScope) -> ()
      | _ -> nyi x.at "outer scope access"
      );
      result
    | Some {it = (s, l); _} ->
      assert (match scope, l with
        ClassScope _, _ | _, DirectLoc _ -> true | _ -> false);
      scope, s, l

let find_typ_var ctxt x envs : scope * T.sort * loc =
  find_var E.find_opt_typ ctxt x envs

let find_var ctxt x envs : scope * T.sort * loc =
  find_var E.find_opt_val ctxt x envs


(* Types *)

let rec compile_typ_var ctxt x ts t' : typ list =
  let emit ctxt = List.iter (emit_instr ctxt x.at) in
  let scope, s, loc = find_typ_var ctxt x ctxt.ext.envs in
  match s with
  | T.LetS ->
    (match scope, loc with
    | PreScope, DirectLoc idx ->
      let t = Source.(@@) (snd (List.nth Prelude.typs (Int32.to_int idx))) x.at in
      t.et <- Some t';
      compile_typ ctxt t
    | (BlockScope | FuncScope), DirectLoc idx ->
      emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    | GlobalScope, DirectLoc idx ->
      emit_instr ctxt x.at W.(global_get (idx @@ x.at));
    | ClassScope _, DirectLoc idx ->  (* in constructor, we have let binding *)
      emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    | ClassScope this_t, InstanceLoc x' ->
      compile_var ctxt (Source.(@@) "this" x.at) this_t;
      let cls = lower_class ctxt x.at (fst (T.as_inst this_t)) in
      let lazy cls_def = cls.def in
      let s, loc = (E.find_typ (Source.(@@) x' x.at) cls_def.env).it in
      assert (s = T.LetS);
      emit ctxt W.[
        struct_get (cls.inst_idx @@ x.at) (as_direct_loc loc @@ x.at)
      ];
    | _ -> assert false
    );
    ts
  | T.FuncS ->
    (match scope with
    | PreScope -> assert false
    | GlobalScope ->
      List.iter (fun tI ->
        compile_typ ctxt tI;
      ) ts;
      emit ctxt W.[call (as_direct_loc loc @@ x.at)]
    | BlockScope | FuncScope | ClassScope _ ->
      nyi x.at "nested type definitions"
(*
      let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
      this.et <- Some this_t;
      compile_exp ctxt
        {e with it = CallE ({e1 with it = DotE (this, x)}, ts, es)}
*)
    );
    []
  | T.ClassS ->
    (match t' with
    | T.Inst (cls, _) ->
      compile_var ctxt x (T.Class cls);
      let idx = lower_var_type ctxt x.at (T.Class cls) in
      emit ctxt W.[
        struct_get (idx @@ x.at) (cls_disp @@ x.at);
      ];
      ts
    | _ -> assert false
    )
  | T.VarS | T.ProhibitedS ->
    assert false

and compile_typ ctxt t =
  assert (not !Flags.parametric);
  let emit ctxt = List.iter (emit_instr ctxt t.at) in
  let ts =
    match type_of t with
    | T.Bool -> emit ctxt W.[i32_const (1l @@ t.at); i31_new]; []
    | T.Byte -> emit ctxt W.[i32_const (2l @@ t.at); i31_new]; []
    | T.Int -> emit ctxt W.[i32_const (3l @@ t.at); i31_new]; []
    | T.Float -> emit ctxt W.[i32_const (4l @@ t.at); i31_new]; []
    | T.Text -> emit ctxt W.[i32_const (5l @@ t.at); i31_new]; []
    | T.Obj -> emit ctxt W.[i32_const (6l @@ t.at); i31_new]; []
    | _ ->
    match t.it with
    | VarT (y, ts) -> compile_typ_var ctxt y ts (type_of t)
    | BoxT t1 ->
      (match type_of t1 with
      | T.Bool -> emit ctxt W.[i32_const (-1l @@ t.at); i31_new]; []
      | T.Byte -> emit ctxt W.[i32_const (-2l @@ t.at); i31_new]; []
      | T.Int -> emit ctxt W.[i32_const (-3l @@ t.at); i31_new]; []
      | T.Float -> emit ctxt W.[i32_const (-4l @@ t.at); i31_new]; []
      | _ -> emit ctxt W.[i32_const (7l @@ t.at); i31_new]; [t1]
      )
    | TupT ts -> emit ctxt W.[i32_const (8l @@ t.at); i31_new]; ts
    | ArrayT t1 -> emit ctxt W.[i32_const (9l @@ t.at); i31_new]; [t1]
    | FuncT (ys, ts1, t2) -> nyi t.at "function types"
    | BoolT | ByteT | IntT | FloatT | TextT | ObjT -> assert false
  in
  if ts <> [] then begin
    let rtt_idx = lower_var_rtt ctxt t.at in
    let tagtmp = emit_local ctxt t.at W.(RefType (Nullable, EqHeapType)) in
    let arrtmp =
      emit_local ctxt t.at W.(RefType (Nullable, DefHeapType (SynVar rtt_idx))) in
    emit ctxt W.[
      local_set (tagtmp @@ t.at);
      i32_const (i32 (List.length ts + 1) @@ t.at);
      rtt_canon (rtt_idx @@ t.at);
      array_new_default (rtt_idx @@ t.at);
      local_tee (arrtmp @@ t.at);
      i32_const (0l @@ t.at);
      local_get (tagtmp @@ t.at);
      array_set (rtt_idx @@ t.at);
    ];
    List.iteri (fun i tI ->
      emit ctxt W.[
        local_get (arrtmp @@ t.at);
        i32_const (i32 (i + 1) @@ tI.at);
      ];
      compile_typ ctxt tI;
      emit ctxt W.[
        array_set (rtt_idx @@ tI.at);
      ]
    ) ts;
    emit ctxt W.[
      local_get (arrtmp @@ t.at);
      ref_as_non_null;
    ]
  end


(* Expressions *)

and compile_lit ctxt l at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match l with
  | NullL -> emit ctxt W.[ref_null (lower_heap_type ctxt at T.Null)]
  | BoolL b -> emit ctxt W.[i32_const ((if b then 1l else 0l) @@ at)]
  | IntL i -> emit ctxt W.[i32_const (i @@ at)]
  | FloatL z -> emit ctxt W.[f64_const (W.F64.of_float z @@ at)]
  | TextL s ->
    let addr = emit_data ctxt at s in
    emit ctxt W.[
      i32_const (addr @@ at);
      i32_const (i32 (String.length s) @@ at);
      call (Intrinsic.compile_text_new ctxt @@ at);
    ]

and compile_var ctxt x t =
  let scope, s, loc = find_var ctxt x ctxt.ext.envs in
  if s <> T.LetS && s <> T.VarS && s <> T.ClassS then nyi x.at "closures";
  (match scope, loc with
  | PreScope, DirectLoc idx ->
    let _, l = List.nth Prelude.vals (Int32.to_int idx) in
    compile_lit ctxt l x.at
  | (BlockScope | FuncScope), DirectLoc idx ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | GlobalScope, DirectLoc idx ->
    emit_instr ctxt x.at W.(global_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | ClassScope _, DirectLoc idx ->  (* in constructor, we have let binding *)
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | ClassScope this_t, InstanceLoc x' ->
    let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
    this.et <- Some this_t;
    compile_exp ctxt
      {it = DotE (this, Source.(x' @@ x.at)); at = x.at; et = Some t}
  | _ -> assert false
  )

and compile_exp ctxt e =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE x ->
    compile_var ctxt x (type_of e)

  | LitE l ->
    compile_lit ctxt l e.at

  | UnE (op, e1) ->
    (match op, type_of e with
    | NegOp, T.Int -> emit ctxt W.[i32_const (0l @@ e.at)]
    | InvOp, T.Int -> emit ctxt W.[i32_const (-1l @@ e.at)]
    | _ -> ()
    );
    compile_exp ctxt e1;
    (match op, type_of e with
    | PosOp, T.Int -> ()
    | PosOp, T.Float -> ()
    | NegOp, T.Int -> emit ctxt W.[i32_sub]
    | NegOp, T.Float -> emit ctxt W.[f64_neg]
    | InvOp, T.Int -> emit ctxt W.[i32_xor]
    | NotOp, T.Bool -> emit ctxt W.[i32_eqz]
    | _ -> assert false
    )

  | BinE (e1, op, e2) ->
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    (match op, type_of e with
    | AddOp, T.Int -> emit ctxt W.[i32_add]
    | SubOp, T.Int -> emit ctxt W.[i32_sub]
    | MulOp, T.Int -> emit ctxt W.[i32_mul]
    | DivOp, T.Int -> emit ctxt W.[i32_div_s]
    | ModOp, T.Int -> emit ctxt W.[i32_rem_s]
    | AndOp, T.Int -> emit ctxt W.[i32_and]
    | OrOp,  T.Int -> emit ctxt W.[i32_or]
    | XorOp, T.Int -> emit ctxt W.[i32_xor]
    | ShlOp, T.Int -> emit ctxt W.[i32_shl]
    | ShrOp, T.Int -> emit ctxt W.[i32_shr_s]
    | AddOp, T.Float -> emit ctxt W.[f64_add]
    | SubOp, T.Float -> emit ctxt W.[f64_sub]
    | MulOp, T.Float -> emit ctxt W.[f64_mul]
    | DivOp, T.Float -> emit ctxt W.[f64_div]
    | AddOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_cat ctxt @@ e.at)]
    | _ -> assert false
    )

  | RelE (e1, op, e2) ->
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    (match op, T.lub (type_of e1) (type_of e2) with
    | EqOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_eq]
    | NeOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_ne]
    | LtOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_lt_s]
    | GtOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_gt_s]
    | LeOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_le_s]
    | GeOp, (T.Int | T.Byte | T.Bool) -> emit ctxt W.[i32_ge_s]
    | EqOp, T.Float -> emit ctxt W.[f64_eq]
    | NeOp, T.Float -> emit ctxt W.[f64_ne]
    | LtOp, T.Float -> emit ctxt W.[f64_lt]
    | GtOp, T.Float -> emit ctxt W.[f64_gt]
    | LeOp, T.Float -> emit ctxt W.[f64_le]
    | GeOp, T.Float -> emit ctxt W.[f64_ge]
    | EqOp, (T.Null | T.Obj | T.Box _ | T.Array _ | T.Inst _) -> emit ctxt W.[ref_eq]
    | NeOp, (T.Null | T.Obj | T.Box _ | T.Array _ | T.Inst _) -> emit ctxt W.[ref_eq; i32_eqz]
    | EqOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_eq ctxt @@ e.at)]
    | NeOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_eq ctxt @@ e.at); i32_eqz]
    | _ -> assert false
    )

  | LogE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(valbt i32t) (fun ctxt ->
      emit ctxt W.[i32_const (0l @@ e1.at)];
      compile_exp ctxt e1;
      emit ctxt W.[i32_eqz; br_if (0l @@ e.at); drop];
      compile_exp ctxt e2;
    )

  | LogE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(valbt i32t) (fun ctxt ->
      emit ctxt W.[i32_const (1l @@ e1.at)];
      compile_exp ctxt e1;
      emit ctxt W.[br_if (0l @@ e.at); drop];
      compile_exp ctxt e2;
    )

  | BoxE e1 ->
    compile_exp ctxt e1;
    (match type_of e1 with
    | T.Bool | T.Byte ->
      emit ctxt W.[i31_new]
    | _ ->
      let typeidx = lower_var_type ctxt e.at (type_of e) in
      compile_coerce_value_type ctxt e1.at (type_of e1);
      emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)]
    )

  | UnboxE e1 ->
    compile_exp ctxt e1;
    (match type_of e with
    | T.Bool | T.Byte ->
      emit ctxt W.[i31_get_u]
    | _ ->
      let typeidx = lower_var_type ctxt e.at (type_of e1) in
      let struct_get_sxopt =
        match type_of e with
        | T.Bool | T.Byte -> W.struct_get_u
        | _ -> W.struct_get
      in
      emit ctxt [struct_get_sxopt (typeidx @@ e.at) (0l @@ e.at)];
      compile_coerce_block_type ctxt e.at (type_of e)
    )

  | TupE [] ->
    ()

  | TupE es ->
    let typeidx = lower_var_type ctxt e.at (type_of e) in
    List.iter (fun eI ->
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (type_of eI);
    ) es;
    emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)]

  | ProjE (e1, n) ->
    let typeidx = lower_var_type ctxt e.at (type_of e1) in
    compile_exp ctxt e1;
    let struct_get_sxopt =
      match type_of e with
      | T.Bool | T.Byte -> W.struct_get_u
      | _ -> W.struct_get
    in
    emit ctxt [struct_get_sxopt (typeidx @@ e.at) (i32 n @@ e.at)];
    compile_coerce_abs_block_type ctxt e.at (type_of e)

  | ArrayE es ->
    let typeidx = lower_var_type ctxt e.at (type_of e) in
    emit ctxt W.[
      i32_const (i32 (List.length es) @@ e.at);
      rtt_canon (typeidx @@ e.at);
      array_new_default (typeidx @@ e.at);
    ];
    let tmpidx =
      if List.length es = 0 then 0l else begin
        let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
        let tmpidx = emit_local ctxt e.at t' in
        emit ctxt W.[local_tee (tmpidx @@ e.at)];
        tmpidx
      end
    in
    List.iteri (fun i eI ->
      emit ctxt W.[local_get (tmpidx @@ e.at); i32_const (i32 i @@ e.at)];
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (type_of eI);
      emit ctxt W.[array_set (typeidx @@ e.at)];
    ) es

  | LenE e1 ->
    let typeidx = lower_var_type ctxt e.at (type_of e1) in
    compile_exp ctxt e1;
    emit ctxt W.[array_len (typeidx @@ e.at)]

  | IdxE (e1, e2) ->
    let typeidx = lower_var_type ctxt e.at (type_of e1) in
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    let array_get_sxopt =
      match type_of e with
      | T.Bool | T.Byte -> W.array_get_u
      | _ -> W.array_get
    in
    emit ctxt [array_get_sxopt (typeidx @@ e.at)];
    compile_coerce_abs_block_type ctxt e.at (type_of e)

  | CallE (e1, ts, es) ->
    let t1 =
      match e1.it with
      | VarE x ->
        let scope, s, loc = find_var ctxt x ctxt.ext.envs in
        (match scope, s with
        | PreScope, _ -> assert false
        | GlobalScope, T.FuncS ->
          let ys, ts1, _ = T.as_func (type_of e1) in
          let subst = T.typ_subst ys (List.map type_of ts) in
          if not !Flags.parametric then begin
            List.iter (fun tI ->
              compile_typ ctxt tI;
            ) ts
          end;
          List.iter2 (fun eI tI ->
            compile_exp ctxt eI;
            compile_coerce_value_type ctxt eI.at (type_of eI);
            compile_coerce_null_type ctxt eI.at (type_of eI) (T.subst subst tI);
          ) es ts1;
          emit ctxt W.[call (as_direct_loc loc @@ x.at)]
        | ClassScope this_t, T.FuncS ->
          let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
          this.et <- Some this_t;
          compile_exp ctxt
            {e with it = CallE ({e1 with it = DotE (this, x)}, ts, es)}
        | _, T.FuncS -> nyi x.at "local function calls"
        | _ -> nyi e.at "indirect function calls"
        );
        type_of e1

      | DotE (e11, x) ->
        let t11 = type_of e11 in
        let cls = lower_class ctxt e11.at (fst (T.as_inst t11)) in
        let lazy cls_def = cls.def in
        let s, loc = (E.find_val x cls_def.env).it in
        let tmpidx = emit_local ctxt e11.at (lower_value_type ctxt e11.at t11) in
        compile_exp ctxt e11;
        emit ctxt W.[local_tee (tmpidx @@ e.at)];
        let ys, ts1, _ = T.as_func (type_of e1) in
        let subst = T.typ_subst ys (List.map type_of ts) in
        if not !Flags.parametric then begin
          List.iter (fun tI ->
            compile_typ ctxt tI;
          ) ts
        end;
        List.iter2 (fun eI tI ->
          compile_exp ctxt eI;
          compile_coerce_value_type ctxt eI.at (type_of eI);
          compile_coerce_null_type ctxt eI.at (type_of eI) (T.subst subst tI);
        ) es ts1;
        (match s with
        | T.FuncS ->
          emit ctxt W.[
            local_get (tmpidx @@ e11.at);
            struct_get (cls.inst_idx @@ e11.at) (0l @@ x.at);
            struct_get (cls.disp_idx @@ e11.at) (as_direct_loc loc @@ x.at);
            call_ref;
          ];
        | T.LetS | T.VarS -> nyi e.at "indirect function calls"
        | T.ClassS -> nyi e.at "nested classes"
        | T.ProhibitedS -> assert false
        );
        let tcls, _ = T.as_inst (type_of e11) in
        (* Find root type *)
        let rec find_root tcls =
          match Option.join (Option.map find_root (T.sup_cls tcls)) with
          | None -> List.assoc_opt x.it tcls.T.def
          | some -> some
        in snd (Option.get (find_root tcls))

      | _ -> nyi e.at "indirect function calls"
    in
    (* TODO: this isn't enough once we have closures or nested classes *)
    let _, _, t = T.as_func t1 in
    if T.is_var t then
      compile_coerce_abs_block_type ctxt e.at (type_of e)

  | NewE (x, ts, es) ->
    let tcls, _ = T.as_inst (type_of e) in
    let cls = lower_class ctxt e.at tcls in
    let subst = T.typ_subst tcls.T.tparams (List.map type_of ts) in
    if not !Flags.parametric then begin
      List.iter (fun tI ->
        compile_typ ctxt tI;
      ) ts
    end;
    List.iter2 (fun eI tI ->
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (type_of eI);
      compile_coerce_null_type ctxt eI.at (type_of eI) (T.subst subst tI);
    ) es tcls.T.vparams;
    compile_var ctxt x (T.Class tcls);
    emit ctxt W.[
      struct_get (cls.cls_idx @@ x.at) (cls_new @@ x.at);
      call_ref;
    ]

  | NewArrayE (t, e1, e2) ->
    let typeidx = lower_var_type ctxt e.at (type_of e) in
    let t' = lower_value_type ctxt e1.at (type_of e1) in
    let tmpidx = emit_local ctxt e1.at t' in
    compile_exp ctxt e1;
    emit ctxt W.[local_set (tmpidx @@ e1.at)];
    compile_exp ctxt e2;
    compile_coerce_value_type ctxt e2.at (type_of e2);
    compile_coerce_null_type ctxt e2.at (type_of e2) (type_of t);
    emit ctxt W.[
      local_get (tmpidx @@ e1.at);
      rtt_canon (typeidx @@ e.at);
      array_new (typeidx @@ e.at);
    ]

  | DotE (e1, x) ->
    let t1 = type_of e1 in
    let cls = lower_class ctxt e1.at (fst (T.as_inst t1)) in
    let lazy cls_def = cls.def in
    let s, loc = (E.find_val x cls_def.env).it in
    compile_exp ctxt e1;
    (match s with
    | T.LetS | T.VarS ->
      let struct_get_sxopt =
        match type_of e with
        | T.Bool | T.Byte -> W.struct_get_u
        | _ -> W.struct_get
      in
      emit ctxt [
        struct_get_sxopt (cls.inst_idx @@ e1.at) (as_direct_loc loc @@ x.at)
      ];
      compile_coerce_abs_block_type ctxt e.at (type_of e)
    | T.FuncS -> nyi e.at "closures"
    | T.ClassS -> nyi e.at "nested classes"
    | T.ProhibitedS -> assert false
    )

  | AssignE (e1, e2) ->
    (match e1.it with
    | VarE x ->
      let scope, s, loc = find_var ctxt x ctxt.ext.envs in
      (match scope with
      | PreScope -> assert false
      | BlockScope | FuncScope ->
        compile_exp ctxt e2;
        compile_coerce_value_type ctxt e2.at (type_of e2);
        compile_coerce_null_type ctxt e2.at (type_of e2) (type_of e1);
        emit_instr ctxt x.at W.(local_set (as_direct_loc loc @@ x.at))
      | GlobalScope ->
        compile_exp ctxt e2;
        compile_coerce_value_type ctxt e2.at (type_of e2);
        compile_coerce_null_type ctxt e2.at (type_of e2) (type_of e1);
        emit_instr ctxt x.at W.(global_set (as_direct_loc loc @@ x.at))
      | ClassScope this_t ->
        let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
        this.et <- Some this_t;
        compile_exp ctxt
          {e with it = AssignE ({e1 with it = DotE (this, x)}, e2)}
      )

    | IdxE (e11, e12) ->
      let typeidx = lower_var_type ctxt e11.at (type_of e11) in
      compile_exp ctxt e11;
      compile_exp ctxt e12;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (type_of e2);
      compile_coerce_null_type ctxt e2.at (type_of e2) (T.as_array (type_of e11));
      emit ctxt W.[array_set (typeidx @@ e.at)]

    | DotE (e11, x) ->
      let t11 = type_of e11 in
      let tcls, _ = T.as_inst t11 in
      let cls = lower_class ctxt e1.at tcls in
      let lazy cls_def = cls.def in
      let s, loc = (E.find_val x cls_def.env).it in
      assert (s = T.VarS);
      compile_exp ctxt e11;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (type_of e2);
      compile_coerce_null_type ctxt e2.at (type_of e2) (snd (List.assoc x.it tcls.T.def));
      emit ctxt W.[
        struct_set (cls.inst_idx @@ e11.at) (as_direct_loc loc @@ x.at)
      ]

    | _ -> assert false
    )

  | AnnotE (e1, t) ->
    compile_exp ctxt e1;
    compile_coerce_null_type ctxt e1.at (type_of e1) (type_of t);

  | CastE (e1, x, ts) ->
    assert (not !Flags.parametric);
    if T.eq (type_of e) T.Obj then begin
      compile_exp ctxt e1;
      compile_coerce_null_type ctxt e1.at (type_of e1) (type_of e);
    end else begin
      let t1' = lower_value_type ctxt e1.at (type_of e1) in
      let t' = lower_value_type ctxt e.at (type_of e) in
      let tcls, _ = T.as_inst (type_of e) in
      let cls = lower_class ctxt e.at tcls in
      let tmpidx = emit_local ctxt e1.at t1' in
      let tmpidx2 = emit_local ctxt e1.at t' in
      let clsidx = emit_local ctxt x.at (lower_value_type ctxt x.at (T.Class tcls)) in
      let bt = lower_block_type ctxt e.at (type_of e) in
      emit_block ctxt e.at W.block bt (fun ctxt ->
        (* Push default null result *)
        emit ctxt W.[
          ref_null (lower_heap_type ctxt e.at (type_of e));
        ];
        (* Compile operand *)
        compile_exp ctxt e1;
        compile_coerce_null_type ctxt e1.at (type_of e1) (type_of e);
        (* Check for null *)
        emit ctxt W.[
          local_tee (tmpidx @@ e1.at);
          ref_is_null;
          br_if (0l @@ e.at);
        ];
        (* Cast down representation type *)
        let bt2 = lower_block_type_func ctxt e.at [type_of e] [type_of e; type_of e] in
        emit_block ctxt e.at W.block bt2 (fun ctxt ->
          emit ctxt W.[
            local_get (tmpidx @@ e1.at);
          ];
          compile_var ctxt x (T.Class tcls);
          emit ctxt W.[
            local_tee (clsidx @@ x.at);
            struct_get (cls.cls_idx @@ x.at) (cls_rtt @@ x.at);
            br_on_cast (0l @@ e.at);
            drop;
            br (1l @@ e.at);
          ];
        );
        (* Check class *)
        let lazy cls_def = cls.def in
        let offset = List.length cls_def.disp_flds - 1 in
        emit ctxt W.[
          local_tee (tmpidx2 @@ e1.at);
          struct_get (cls.inst_idx @@ e1.at) (0l @@ e1.at);
          struct_get (cls.disp_idx @@ x.at) (i32 offset @@ x.at);
          local_get (clsidx @@ x.at);
          struct_get (cls.cls_idx @@ x.at) (cls_disp @@ x.at);
          ref_eq;
          i32_eqz;
          br_if (0l @@ e.at);
        ];
        (* Check generic arguments *)
        let start = cls_first_inst_idx cls in
        List.iteri (fun i t ->
          compile_typ ctxt t;
          emit ctxt W.[
            local_get (tmpidx2 @@ e1.at);
            struct_get (cls.inst_idx @@ x.at) (i32 (i + start) @@ x.at);
            call (Intrinsic.compile_rtt_eq ctxt @@ t.at);
            i32_eqz;
            br_if (0l @@ e.at);
          ];
        ) ts;
        (* Return result *)
        emit ctxt W.[
          drop;
          local_get (tmpidx2 @@ e1.at);
        ]
      )
    end

  | AssertE e1 ->
    compile_exp ctxt e1;
    emit ctxt W.[
      i32_eqz;
      if_ W.voidbt [unreachable @@ e.at] []
    ]

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at (type_of e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      emit_block ctxt e.at W.block W.voidbt (fun ctxt ->
        compile_exp ctxt e1;
        emit ctxt W.[i32_eqz; br_if (0l @@ e.at)];
        compile_exp ctxt e2;
        emit ctxt W.[br (1l @@ e.at)];
      );
      compile_exp ctxt e3;
    )

  | WhileE (e1, e2) ->
    emit_block ctxt e.at W.block W.voidbt (fun ctxt ->
      emit_block ctxt e.at W.loop W.voidbt (fun ctxt ->
        compile_exp ctxt e1;
        emit ctxt W.[i32_eqz; br_if (1l @@ e.at)];
        compile_exp ctxt e2;
        emit ctxt W.[br (0l @@ e.at)];
      );
    )

  | RetE e1 ->
    compile_exp ctxt e1;
    compile_coerce_null_type ctxt e1.at (type_of e1) ctxt.ext.ret;
    emit ctxt W.[return]

  | BlockE ds ->
    compile_block (enter_scope ctxt BlockScope) ds


(* Declarations *)

(*
 * Block and function scopes are compiled in two passes:
 * 1. alloc funcs, assigning function indices (to deal with mutual recursion)
 * 2. FullPass, actually compiling everything
 *
 * Class scopes are compiled in four passes:
 * 1. alloc funcs, assigning function indices
 * 2. FuncPass, compiling the methods (invoked as part of class declaration)
 * 3. LetPass, compiling let initialisation (invoked when compiling the constructor)
 * 4. VarPass, compiling var initialisation and exp (likewise)
 *)

and alloc_funcdec ctxt d =
  let scope, env = current_scope ctxt in
  match d.it with
  | ExpD _ | LetD _ | VarD _ ->
    ()

  | TypD (x, _, _) ->
    if not !Flags.parametric then begin
      let idx, define = emit_func_deferred ctxt d.at in
      ctxt.ext.funcs := FuncEnv.add idx define !(ctxt.ext.funcs);
      env := E.extend_typ !env x (T.FuncS, DirectLoc idx)
    end

  | FuncD (x, _, _, _, _) ->
    let idx, define = emit_func_deferred ctxt d.at in
    ctxt.ext.funcs := FuncEnv.add idx define !(ctxt.ext.funcs);
    env := E.extend_val !env x (T.FuncS, DirectLoc idx)

  | ClassD (x, _, _, _, _) ->
    let tcls = T.as_class (bind_type_of d) in
    let cls = lower_class ctxt d.at tcls in
    let cls_ht = W.(DefHeapType (SynVar cls.cls_idx)) in
    let cls_vt = W.(RefType (Nullable, cls_ht)) in
    let idx =
      match scope with
      | BlockScope | FuncScope -> emit_local ctxt x.at cls_vt
      | GlobalScope ->
        let const = W.[ref_null cls_ht @@ d.at] @@ d.at in
        emit_global ctxt x.at W.Mutable cls_vt const
      | ClassScope _ -> nyi d.at "nested class definitions"
      | PreScope -> assert false
    in

    let new_idx, define_new = emit_func_deferred ctxt d.at in
    let pre_alloc_idx, define_pre_alloc = emit_func_deferred ctxt d.at in
    let post_alloc_idx, define_post_alloc = emit_func_deferred ctxt d.at in
    let lazy cls_def = cls.def in
    cls_def.new_idx <- new_idx;
    cls_def.pre_alloc_idx <- pre_alloc_idx;
    cls_def.post_alloc_idx <- post_alloc_idx;
    ctxt.ext.funcs := !(ctxt.ext.funcs)
      |> FuncEnv.add new_idx define_new
      |> FuncEnv.add pre_alloc_idx define_pre_alloc
      |> FuncEnv.add post_alloc_idx define_post_alloc;

    if not !Flags.parametric then begin
      env := E.extend_typ !env x (T.ClassS, DirectLoc idx)
    end;
    env := E.extend_val !env x (T.ClassS, DirectLoc idx)


and compile_dec pass ctxt d =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
  let scope, env = current_scope ctxt in
  let t = bind_type_of d in
  match d.it with
  | ExpD _ when pass = FuncPass || pass = LetPass ->
    ()

  | ExpD e ->
    compile_exp ctxt e

  | LetD (x, _e) when pass = FuncPass || pass = VarPass ->
    env := E.extend_val !env x (T.LetS, InstanceLoc x.it)

  | LetD (x, e) ->
    compile_exp ctxt e;
    compile_coerce_value_type ctxt e.at t;
    let t' = lower_value_type ctxt x.at t in
    let loc =
      match scope with
      | PreScope -> assert false

      | BlockScope | FuncScope ->
        assert (pass = FullPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_set (idx @@ x.at)];
        DirectLoc idx

      | GlobalScope ->
        assert (pass = FullPass);
        let const = default_const ctxt x.at t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        emit ctxt W.[global_set (idx @@ x.at)];
        DirectLoc idx

      | ClassScope _ ->
        assert (pass = LetPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_tee (idx @@ x.at)];
        DirectLoc idx
    in
    env := E.extend_val !env x (T.LetS, loc)

  | VarD (x, _, _e) when pass = LetPass ->
    emit ctxt (default_exp ctxt x.at t)

  | VarD (x, _, _e) when pass = FuncPass ->
    env := E.extend_val !env x (T.VarS, InstanceLoc x.it)

  | VarD (x, _, e) ->
    let t' = lower_value_type ctxt x.at t in
    let loc =
      match scope with
      | PreScope -> assert false

      | BlockScope | FuncScope ->
        assert (pass = FullPass);
        let idx = emit_local ctxt x.at t' in
        compile_exp ctxt e;
        compile_coerce_value_type ctxt e.at t;
        compile_coerce_null_type ctxt e.at (type_of e) t;
        emit ctxt W.[local_set (idx @@ d.at)];
        DirectLoc idx

      | GlobalScope ->
        assert (pass = FullPass);
        let const = default_const ctxt x.at t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        compile_exp ctxt e;
        compile_coerce_value_type ctxt e.at t;
        compile_coerce_null_type ctxt e.at (type_of e) t;
        emit ctxt W.[global_set (idx @@ d.at)];
        DirectLoc idx

      | ClassScope this_t ->
        assert (pass = VarPass);
        let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
        let dot = Source.(DotE (this, x) @@ x.at) in
        let assign = Source.(AssignE (dot, e) @@ d.at) in
        this.et <- Some this_t;
        dot.et <- Some t;
        assign.et <- Some (result_type_of d);
        compile_exp ctxt assign;
        InstanceLoc x.it
    in
    env := E.extend_val !env x (T.VarS, loc)

  | TypD _ when pass = LetPass ->
    ()

  | TypD (x, _ys, _t) when pass = VarPass ->
    if not !Flags.parametric then begin
      env := E.extend_typ !env x (T.FuncS, InstanceLoc x.it)
    end

  | TypD (x, ys, t) ->
    if not !Flags.parametric then begin
      let t2' = lower_value_rtt ctxt x.at in
      let ts1 = List.map (fun _ -> t2') ys in
      let ts1' =
        if pass <> FuncPass then ts1 else
        let tcls = Option.get ctxt.ext.tcls in
        let cls = lower_class ctxt x.at tcls in
        W.(RefType (Nullable, DefHeapType (SynVar cls.inst_idx))) :: ts1
      in
      let idx =
        match (E.find_typ x !env).it with
        | (T.FuncS, DirectLoc idx) -> idx
        | _ -> assert false
      in
      FuncEnv.find idx !(ctxt.ext.funcs) ctxt ts1' [t2']
        (fun ctxt idx ->
          let _, env' = current_scope ctxt in
          env' := E.extend_typ !env' x (T.FuncS, DirectLoc idx);
          let ctxt = enter_scope ctxt FuncScope in
          let _, env = current_scope ctxt in
          let this = if pass = FuncPass then emit_param ctxt x.at else -1l in
          List.iter (fun yI ->
            let idx = emit_param ctxt yI.at in
            env := E.extend_typ !env yI (T.LetS, DirectLoc idx)
          ) ys;
          if pass = FuncPass then begin
            env :=
              E.extend_val !env Source.("this" @@ x.at) (T.LetS, DirectLoc this)
          end;
          compile_typ ctxt t
        )
    end

  | FuncD _ when pass = LetPass ->
    ()

  | FuncD (x, _ys, _xts, _t, _e) when pass = VarPass ->
    env := E.extend_val !env x (T.FuncS, InstanceLoc x.it)

  | FuncD (x, ys, xts, tr, e) ->
    let W.FuncType (ts1, ts2) = lower_func_type ctxt d.at t in
    let ts1', ts2', override_opt =
      if pass <> FuncPass then ts1, ts2, None else
      let tcls = Option.get ctxt.ext.tcls in
      let cls = lower_class ctxt x.at tcls in
      let lazy cls_def = cls.def in
      let this_t = W.(RefType (Nullable, DefHeapType (SynVar cls.inst_idx))) in
      match List.find_opt (fun (_, (x', _)) -> x' = x.it) cls_def.overrides with
      | Some (_, (_, W.FuncType (ts1', ts2'))) ->
        ts1', ts2', Some (tcls, cls, this_t, List.tl ts1')
      | None -> this_t::ts1, ts2, None
    in
    let idx =
      match (E.find_val x !env).it with
      | (T.FuncS, DirectLoc idx) -> idx
      | _ -> assert false
    in
    FuncEnv.find idx !(ctxt.ext.funcs) ctxt ts1' ts2'
      (fun ctxt idx ->
        let _, env' = current_scope ctxt in
        env' := E.extend_val !env' x (T.FuncS, DirectLoc idx);
        let ctxt = enter_scope ctxt FuncScope in
        let ctxt = {ctxt with ext = {ctxt.ext with ret = type_of tr}} in
        let _, env = current_scope ctxt in
        let this_param = if pass = FuncPass then emit_param ctxt x.at else -1l in
        if not !Flags.parametric then begin
          List.iter (fun yI ->
            let idx = emit_param ctxt yI.at in
            env := E.extend_typ !env yI (T.LetS, DirectLoc idx);
          ) ys
        end;
        List.iter (fun (xI, _) ->
          let idx = emit_param ctxt xI.at in
          env := E.extend_val !env xI (T.LetS, DirectLoc idx)
        ) xts;
        if pass = FuncPass then begin
          let this =
            match override_opt with
            | None -> this_param
            | Some (tcls, cls, this_t, param_ts) ->
              (* Downcast this *)
              let this = emit_local ctxt x.at this_t in
              emit ctxt W.[
                local_get (this_param @@ x.at);
              ];
              compile_var ctxt Source.(ctxt.ext.self @@ x.at) (T.Class tcls);
              emit ctxt W.[
                struct_get (cls.cls_idx @@ x.at) (cls_rtt @@ x.at);
                ref_cast;
                local_set (this @@ x.at);
              ];
              (* Downcast params if necessary (non-generic override of generic method) *)
              let offset = if !Flags.parametric then 0 else List.length ys in
              let i = ref (1 + offset) in
              List.iter2 (fun (x, t) param_t ->
                let t' = lower_value_type ctxt t.at (type_of t) in
                if t' <> param_t then begin
                  let local = emit_local ctxt x.at t' in
                  env := E.extend_val !env x (T.LetS, DirectLoc local);
                  emit ctxt W.[
                    local_get (i32 !i @@ x.at);
                  ];
                  compile_coerce_abs_value_type ctxt x.at (type_of t);
                  emit ctxt W.[
                    local_set (local @@ x.at);
                  ]
                end;
                incr i
              ) xts (W.Lib.List.drop offset param_ts);
              this
          in
          env :=
            E.extend_val !env Source.("this" @@ x.at) (T.LetS, DirectLoc this)
        end;
        compile_exp ctxt e;
        compile_coerce_null_type ctxt e.at (type_of e) (type_of tr)
      )

  | ClassD _ when pass <> FullPass ->
    nyi d.at "nested class definitions"

  | ClassD (x, ys, xts, sup_opt, ds) ->
    let tcls = T.as_class t in
    let cls = lower_class ctxt d.at tcls in
    let lazy cls_def = cls.def in
    let cls_ht = W.(DefHeapType (SynVar cls.cls_idx)) in
    let cls_vt = W.(RefType (Nullable, cls_ht)) in
    let inst_t = T.Inst (tcls, List.map T.var tcls.T.tparams) in
    let inst_vt = lower_value_type ctxt d.at inst_t in

    let idx =
      match (E.find_val x !env).it with
      | (T.ClassS, DirectLoc idx) -> idx
      | _ -> assert false
    in

    (* Set up scope environment *)
    let ctxt = enter_scope ctxt (ClassScope inst_t) in
    let _, env = current_scope ctxt in

    Option.iter (fun sup ->
      let lazy sup_def = sup.def in
      env := E.adjoin !env
        (E.mapi_typs (fun x (s, _) -> (s, InstanceLoc x))
          (E.mapi_vals (fun x (s, _) -> (s, InstanceLoc x))
            sup_def.env));
    ) cls.sup;
    let own_start =
      match cls.sup with
      | None -> 1
      | Some {def = lazy sup_def; _} -> List.length sup_def.inst_flds + 1
    in
    (* In methods, class parameters are mapped to hidden fields, using an 
     * indirection through a hidden field name. *)
    let offset = if !Flags.parametric then 0 else List.length ys in
    if not !Flags.parametric then begin
      List.iteri (fun i yI ->
        let i' = i32 (own_start + i) in
        let y' = hidden i' in
        env := E.extend_typ !env Source.(y' @@ x.at) (T.LetS, DirectLoc i');
        env := E.extend_typ !env yI (T.LetS, InstanceLoc y');
      ) ys
    end;
    List.iteri (fun i (xI, _) ->
      let i' = i32 (own_start + offset + i) in
      let x' = hidden i' in
      env := E.extend_val !env Source.(x' @@ x.at) (T.LetS, DirectLoc i');
      env := E.extend_val !env xI (T.LetS, InstanceLoc x');
    ) xts;

    let save_env = !env in

    (* Compile own functions *)
    let ctxt = {ctxt with ext = {ctxt.ext with self = x.it; tcls = Some tcls}} in
    List.iter (alloc_funcdec ctxt) ds;
    compile_decs FuncPass ctxt ds;
    let func_env = !env in
    env := save_env;

    (* Construct dispatch table *)
    (* First, bind and push parent functions, or overrides *)
    let suptmp, sup_at, sup_cls, sup_def, sup_t, sup_vt =
      match sup_opt with
      | None -> -1l, no_region, cls, cls_def, T.Bot, W.i32t
      | Some sup ->
        let (x2, _, _) = sup.it in
        let sup_cls = lower_class ctxt x2.at (type_of sup) in
        let lazy sup_def = sup_cls.def in
        let sup_t = T.Class (type_of sup) in
        let sup_ht = W.(DefHeapType (SynVar sup_cls.cls_idx)) in
        let sup_vt = W.(RefType (Nullable, sup_ht)) in

        (* Load class *)
        let suptmp = emit_local ctxt x2.at sup_vt in
        compile_var ctxt x2 sup_t;

        (* Push all entries from dispatch table and table itself *)
        if sup_def.disp_flds = [] then
          emit ctxt W.[
            local_set (suptmp @@ x2.at);
          ]
        else begin
          let disp_ht = W.(DefHeapType (SynVar sup_cls.disp_idx)) in
          let disptmp = emit_local ctxt x2.at W.(RefType (Nullable, disp_ht)) in
          emit ctxt W.[
            local_tee (suptmp @@ x2.at);
            struct_get (sup_cls.cls_idx @@ x2.at) (cls_disp @@ x2.at);
            local_set (disptmp @@ x2.at);
          ];

          List.iteri (fun i _ ->
            match List.assoc_opt (i32 i) cls_def.overrides with
            | None ->
              emit ctxt W.[
                local_get (disptmp @@ x2.at);
                struct_get (sup_cls.disp_idx @@ x2.at) (i32 i @@ x2.at);
              ];
            | Some (x, _) ->
              let _, loc = (E.find_val Source.(x @@ x2.at) func_env).it in
              emit_func_ref ctxt d.at (as_direct_loc loc);
              emit ctxt W.[ref_func (as_direct_loc loc @@ d.at)]
          ) sup_def.disp_flds;
        end;

        suptmp, x2.at, sup_cls, sup_def, sup_t, sup_vt
    in

    (* Second, push own functions, minus overrides *)
    List.iter (fun (x, sl) ->
      match sl.it with
      | T.FuncS, DirectLoc i
        when not (List.exists (fun (_, (x', _)) -> x = x') cls_def.overrides) ->
        emit_func_ref ctxt d.at i;
        emit ctxt W.[ref_func (i @@ d.at)]
      | _ -> ()
    ) (E.sorted_vals func_env);

    (* Third, push place holder for own class *)
    let disp_ht = W.(DefHeapType (SynVar cls.disp_idx)) in
    if not !Flags.parametric then
      emit ctxt W.[
        ref_null disp_ht;
      ];

    (* Fourth, allocate dispatch table (and leave on stack) *)
    emit ctxt W.[
      rtt_canon (cls.disp_idx @@ d.at);
      struct_new (cls.disp_idx @@ d.at);
    ];

    (* Finally, tie knot for dispatch table *)
    if not !Flags.parametric then begin
      let disptmp = emit_local ctxt d.at W.(RefType (Nullable, disp_ht)) in
      let lazy cls_def = cls.def in
      let offset = List.length cls_def.disp_flds - 1 in
      emit ctxt W.[
        local_tee (disptmp @@ d.at);
        local_get (disptmp @@ d.at);
        struct_set (cls.disp_idx @@ d.at) (i32 offset @@ d.at);
        local_get (disptmp @@ d.at);
        ref_as_non_null;
      ]
    end;

    (* Allocate RTT (and leave on stack) *)
    if sup_opt = None then
      emit ctxt W.[
        rtt_canon (lower_var_type ctxt d.at T.Obj @@ d.at)
      ]
    else begin
      emit ctxt W.[
        local_get (suptmp @@ sup_at);
        struct_get (sup_cls.cls_idx @@ sup_at) (cls_rtt @@ sup_at);
      ]
    end;
    emit ctxt W.[
      rtt_sub (cls.inst_idx @@ d.at);
    ];

    (* Emit pre-alloc function *)
    FuncEnv.find cls_def.pre_alloc_idx !(ctxt.ext.funcs) ctxt
      cls_def.param_vals (List.map snd cls_def.pre_vals)
      (fun ctxt _ ->
        if not !Flags.parametric then begin
          List.iter (fun yI ->
            let idx = emit_param ctxt yI.at in
            env := E.extend_typ !env yI (T.LetS, DirectLoc idx);
          ) ys
        end;
        List.iter (fun (xI, _) ->
          let idx = emit_param ctxt xI.at in
          env := E.extend_val !env xI (T.LetS, DirectLoc idx);
        ) xts;

        (* Invoke parent pre-alloc *)
        let sup_pre_vals, sup_at =
          match sup_opt with
          | None -> [], no_region
          | Some sup ->
            let (x2, ts2, es2) = sup.it in
            if not !Flags.parametric then begin
              List.iter (compile_typ ctxt) ts2
            end;
            List.iter (compile_exp ctxt) es2;
            compile_var ctxt x sup_t;
            emit ctxt W.[
              struct_get (cls.cls_idx @@ x2.at) (cls_sup @@ x2.at);
              struct_get (sup_cls.cls_idx @@ d.at) (cls_pre_alloc @@ d.at);
              call_ref;
            ];
            sup_def.pre_vals, sup.at
        in

        (* Return (parent's and) own parameters and let values *)
        (* Bind parent's let values to locals if necessary *)
        let _, sup_let_depth =
          List.fold_right (fun (x, _t) (i, max) ->
            (i + 1, if is_hidden x then max else i)
          ) sup_pre_vals (1, 0)
        in
        let offset = if !Flags.parametric then 0 else List.length ys in
        if sup_let_depth = 0 then begin
          if not !Flags.parametric then begin
            List.iteri (fun i yI ->
              emit ctxt W.[local_get (i32 i @@ yI.at)]
            ) ys;
          end;
          List.iteri (fun i (x, _) ->
            emit ctxt W.[local_get (i32 (i + offset) @@ x.at)]
          ) xts;
          compile_decs LetPass ctxt ds;
        end else begin
          let rest_len = List.length sup_pre_vals - sup_let_depth in
          let locals = W.Lib.List.drop rest_len sup_pre_vals in
          let results = W.Lib.List.drop rest_len cls_def.pre_vals in
          let ft = W.FuncType ([], List.map snd results) in
          let bt = W.(varbt (emit_type ctxt sup_at (FuncDefType ft))) in
          emit_let ctxt sup_at bt (List.map snd locals) (fun ctxt ->
            List.iteri (fun i (xI, _) ->
              let loc = DirectLoc (i32 i) in
              env := E.extend_val !env Source.(xI @@ sup_at) (T.LetS, loc);
              emit ctxt W.[local_get (i32 i @@ sup_at)]
            ) locals;
            if not !Flags.parametric then begin
              List.iteri (fun i yI ->
                let loc = DirectLoc (i32 (i + sup_let_depth)) in
                env := E.extend_typ !env yI (T.LetS, loc);
                emit ctxt W.[local_get (i32 (i + sup_let_depth) @@ yI.at)]
              ) ys;
            end;
            List.iteri (fun i (xI, _) ->
              let loc = DirectLoc (i32 (i + offset + sup_let_depth)) in
              env := E.extend_val !env xI (T.LetS, loc);
              emit ctxt W.[local_get (i32 (i + offset + sup_let_depth) @@ xI.at)]
            ) xts;
            compile_decs LetPass ctxt ds;
          )
        end;

        env := save_env
      );

    (* Emit post-alloc function *)
    FuncEnv.find cls_def.post_alloc_idx !(ctxt.ext.funcs) ctxt [inst_vt] []
      (fun ctxt _ ->
        let this = emit_param ctxt d.at in

        (* Call parent post-alloc *)
        Option.iter (fun sup ->
          emit ctxt W.[
            local_get (this @@ d.at);
          ];
          compile_var ctxt x sup_t;
          emit ctxt W.[
            struct_get (cls.cls_idx @@ d.at) (cls_sup @@ d.at);
            struct_get (sup_cls.cls_idx @@ d.at) (cls_post_alloc @@ d.at);
            call_ref;
          ];
        ) sup_opt;

        (* Run variable initializers *)
        env := E.extend_val !env Source.("this" @@ d.at)
          (T.LetS, DirectLoc this);
        compile_decs VarPass ctxt ds;

        env := save_env
      );

    (* Emit constructor function *)
    let W.FuncType (ts1', ts2') = lower_func_type ctxt d.at (T.Class tcls) in
    FuncEnv.find cls_def.new_idx !(ctxt.ext.funcs) ctxt ts1' ts2'
      (fun ctxt _ ->
        if not !Flags.parametric then begin
          List.iter (fun yI -> ignore (emit_param ctxt yI.at)) ys
        end;
        List.iter (fun (xI, _) -> ignore (emit_param ctxt xI.at)) xts;
        let self = emit_local ctxt d.at cls_vt in
        let this = emit_local ctxt d.at inst_vt in

        (* Load self descriptor *)
        compile_var ctxt x (T.Class tcls);

        (* Prepare dispatch table *)
        emit ctxt W.[
          local_tee (self @@ d.at);
          struct_get (cls.cls_idx @@ d.at) (cls_disp @@ d.at);
        ];

        (* Call pre-alloc function *)
        let i = ref 0 in
        if not !Flags.parametric then begin
          List.iter (fun yI ->
            emit ctxt W.[local_get (i32 !i @@ yI.at)];
            incr i
          ) ys;
        end;
        List.iter (fun (xI, _) ->
          emit ctxt W.[local_get (i32 !i @@ xI.at)];
          incr i
        ) xts;
        emit ctxt W.[
          local_get (self @@ d.at);
          struct_get (cls.cls_idx @@ d.at) (cls_pre_alloc @@ d.at);
          call_ref;
        ];

        (* Alloc instance *)
        emit ctxt W.[
          local_get (self @@ d.at);
          struct_get (cls.cls_idx @@ d.at) (cls_rtt @@ d.at);
          struct_new (cls.inst_idx @@ d.at);
          local_tee (this @@ x.at);
        ];

        (* Call post-alloc function *)
        emit ctxt W.[
          local_get (self @@ d.at);
          struct_get (cls.cls_idx @@ d.at) (cls_post_alloc @@ d.at);
          call_ref;
        ];

        (* Return *)
        emit ctxt W.[
          local_get (this @@ d.at);
        ];
      );

    (* Construct class record (dispatch table is still on stack) *)
    assert (cls_disp = 0l);
    assert (cls_rtt == 1l);
    assert (cls_new == 2l);
    assert (cls_pre_alloc == 3l);
    assert (cls_post_alloc == 4l);
    assert (cls_sup == 5l);
    emit_func_ref ctxt d.at cls_def.new_idx;
    emit_func_ref ctxt d.at cls_def.pre_alloc_idx;
    emit_func_ref ctxt d.at cls_def.post_alloc_idx;
    emit ctxt W.[
      ref_func (cls_def.new_idx @@ d.at);
      ref_func (cls_def.pre_alloc_idx @@ d.at);
      ref_func (cls_def.post_alloc_idx @@ d.at);
    ];
    (if sup_opt = None then
      emit ctxt W.[i32_const (0l @@ d.at)]
    else
      emit ctxt W.[local_get (suptmp @@ sup_at); ref_as_non_null]  (* TODO *)
    );
    emit ctxt W.[
      rtt_canon (cls.cls_idx @@ d.at);
      struct_new (cls.cls_idx @@ d.at);
    ];

    (* Store in target variable *)
    (match scope with
    | BlockScope | FuncScope -> emit ctxt W.[local_set (idx @@ d.at)]
    | GlobalScope -> emit ctxt W.[global_set (idx @@ d.at)]
    | ClassScope _ -> nyi d.at "nested class definitions"
    | PreScope -> assert false
    )


and compile_decs pass ctxt ds =
  match ds with
  | [] -> ()
  | [d] -> compile_dec pass ctxt d
  | d::ds' ->
    compile_dec pass ctxt d;
    if result_type_of d <> T.Tup [] then emit_instr ctxt d.at W.(drop);
    compile_decs pass ctxt ds'


and compile_block ctxt ds =
  List.iter (alloc_funcdec ctxt) ds;
  compile_decs FullPass ctxt ds


(* Programs *)

let compile_imp ctxt d =
  let ImpD (xo, xs, url) = d.it in
  let _, env = current_scope ctxt in
  let x = (match xo with None -> "" | Some x -> x.it ^ "_") in
  List.iter2 (fun xI (st_opt, k_opt) ->
    let x' = Source.((x ^ xI.it) @@ xI.at) in
    let class_opt =
      match st_opt with
      | None -> None
      | Some (sort, t) ->
        let idx =
          match sort with
          | T.LetS | T.VarS ->
            emit_global_import ctxt xI.at url xI.it W.Mutable
              (lower_value_type ctxt xI.at t);
          | T.FuncS ->
            emit_func_import ctxt xI.at url xI.it
              (lower_func_type ctxt xI.at t);
          | T.ClassS ->
            emit_global_import ctxt xI.at url xI.it W.Mutable
              (lower_value_type ctxt xI.at t)
          | T.ProhibitedS -> assert false
        in
        env := E.extend_val !env x' (sort, DirectLoc idx);
        if sort = T.ClassS then Some idx else None
    in
    if not !Flags.parametric then begin
      match k_opt with
      | None -> ()
      | Some k ->
        let idx, sort =
          match class_opt with
          | Some idx -> idx, T.ClassS
          | None ->
            let t2' = lower_value_rtt ctxt xI.at in
            let ts1' = List.init k (fun _ -> t2') in
            let ft = W.FuncType (ts1', [t2']) in
            emit_func_import ctxt xI.at url ("type " ^ xI.it) ft, T.FuncS
        in
        env := E.extend_typ !env x' (sort, DirectLoc idx)
    end
  ) xs (type_of d)

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let emit ctxt = emit_instr ctxt p.at in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
  List.iter (compile_imp ctxt) is;
  let t' = lower_value_type ctxt p.at (type_of p) in
  let const = default_const ctxt p.at (type_of p) in
  let result_idx = emit_global ctxt p.at W.Mutable t' const in
  let start_idx =
    emit_func ctxt p.at [] [] (fun ctxt _ ->
      compile_block ctxt ds;
      compile_coerce_value_type ctxt p.at (type_of p);
      emit ctxt W.(global_set (result_idx @@ p.at));
    )
  in
  emit_start ctxt p.at start_idx;
  emit_global_export ctxt p.at "return" result_idx;
  let _, env = current_scope ctxt in
  if not !Flags.parametric then begin
    E.iter_typs (fun x sl ->
      let sort, loc = sl.it in
      let idx = as_direct_loc loc in
      match sort with
      | T.FuncS -> emit_func_export ctxt sl.at ("type " ^ x) idx
      | T.ClassS -> ()
      | T.LetS | T.VarS | T.ProhibitedS -> assert false
    ) !env;
  end;
  E.iter_vals (fun x sl ->
    let sort, loc = sl.it in
    let idx = as_direct_loc loc in
    match sort with
    | T.LetS | T.VarS | T.ClassS -> emit_global_export ctxt sl.at x idx
    | T.FuncS -> emit_func_export ctxt sl.at x idx
    | T.ProhibitedS -> assert false
  ) !env;
  Emit.gen_module ctxt p.at
