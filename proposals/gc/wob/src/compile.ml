open Source
open Syntax

module T = Type
module E = Env

module W =
struct
  include Wasm
  include Wasm.Ast
  include Wasm.Types
  include Wasm.Value
  include Wasm.Operators
end


(* Helpers *)

let (@@) = Wasm.Source.(@@)

let _f64 = W.F64.of_float
let i32 = W.I32.of_int_s
let (+%) = Int32.add
let (-%) = Int32.sub
let (/%) = Int32.div


(* Failure *)

exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Environment *)

type env = (T.sort * int32, int32) E.env
type scope =
  PreScope | GlobalScope | BlockScope | FuncScope | ClassScope of T.typ

let hidden_prefix = "hidden-"
let hidden_length = String.length hidden_prefix
let hidden i = "hidden-" ^ Int32.to_string i
let is_hidden x = x > "hidden-" && x < "hidden."
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
    env := E.extend_typ !env Source.(y @@ Prelude.region) (i32 i)
  ) Prelude.typs;
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region) (T.LetS, i32 i)
  ) Prelude.vals;
  env

type pass = FullPass | FuncPass | LetPass | VarPass


(* Class table *)

module ClsEnv = Map.Make(Int)

type cls =
  { sup : cls option;
    inst_idx : int32;
    disp_idx : int32;
    cls_idx : int32;
    mutable env : env;
    mutable inst_flds : W.field_type list;
    mutable disp_flds : W.field_type list;
    mutable param_vals : W.value_type list;
    mutable pre_vals : (string * W.value_type) list;
    mutable overrides : (int32 * (string * W.value_type)) list;
  }

type cls_env = cls ClsEnv.t

let make_cls sup inst_idx disp_idx cls_idx =
  { sup;
    inst_idx;
    disp_idx;
    cls_idx;
    inst_flds = [];
    disp_flds = [];
    param_vals = [];
    pre_vals = [];
    overrides = [];
    env = E.empty;
  }


(* Compilation context *)

module DefTypes = Map.Make(struct type t = W.def_type let compare = compare end)

type 'a entities = {mutable list : 'a option ref list; mutable cnt : int32}

type ctxt =
  { envs : (scope * env ref) list;
    clss : cls_env ref;
    self : string;
    tcls : T.cls option;
    deftypes : int32 DefTypes.t ref;
    types : W.type_ entities;
    globals : W.global entities;
    funcs : W.func entities;
    datas : W.data_segment entities;
    imports : W.import entities;
    exports : W.export entities;
    locals : W.local entities;
    instrs : W.instr entities;
    refs : int32 list ref;
    data_offset : int32 ref;
    text_new : int32 option ref;
    text_cat : int32 option ref;
    text_cpy : int32 option ref;
    text_cmp : int32 option ref;
  }

let make_entities () = {list = []; cnt = 0l}
let get_entities ents = List.rev (List.map (fun r -> Option.get !r) ents.list)

let alloc_entity ents : int32 * 'a option ref =
  let idx = ents.cnt in
  let r = ref None in
  ents.cnt <- idx +% 1l;
  ents.list <- r :: ents.list;
  idx, r

let define_entity r ent =
  r := Some ent

let emit_entity ents ent : int32 =
  let idx, r = alloc_entity ents in
  define_entity r ent;
  idx

let implicit_entity ents : int32 =
  let idx = ents.cnt in
  ents.cnt <- idx +% 1l;
  idx

let make_ctxt () =
  { envs = [(PreScope, make_env ())];
    clss = ref ClsEnv.empty;
    self = "";
    tcls = None;
    deftypes = ref DefTypes.empty;
    types = make_entities ();
    globals = make_entities ();
    funcs = make_entities ();
    datas = make_entities ();
    imports = make_entities ();
    exports = make_entities ();
    locals = make_entities ();
    instrs = make_entities ();
    refs = ref [];
    data_offset = ref 0l;
    text_new = ref None;
    text_cat = ref None;
    text_cpy = ref None;
    text_cmp = ref None;
  }

let enter_scope ctxt scope =
  {ctxt with envs = (scope, ref E.empty) :: ctxt.envs}


let lookup_def_type ctxt idx =
  (Option.get !(W.Lib.List32.nth (List.rev ctxt.types.list) idx)).W.Source.it

let lookup_field_type ctxt idx i =
  match lookup_def_type ctxt idx with
  | W.(StructDefType (StructType fts)) ->
    let W.FieldType (t, _) = W.Lib.List32.nth fts i in
    (match t with
    | W.ValueStorageType t -> t
    | _ -> assert false
    )
  | _ -> assert false

let lookup_ref_field_type ctxt idx i =
  match lookup_field_type ctxt idx i with
  | W.(RefType (_, DefHeapType (SynVar idx'))) -> idx'
  | _ -> assert false

let lookup_param_type ctxt idx i =
  match lookup_def_type ctxt idx with
  | W.(FuncDefType (FuncType (ts, _))) -> List.nth ts i
  | _ -> assert false


(* Debug printing *)

let string_of_sort = function
  | T.LetS -> "let"
  | T.VarS -> "var"
  | T.FuncS -> "func"
  | T.ClassS -> "class"
  | T.ProhibitedS -> "prohibited"

let print_env env =
  E.iter_vals (fun x si -> let s, i = si.it in
    Printf.printf " %s(%s)=%s" (string_of_sort s) x (Int32.to_string i)) env;
  Printf.printf "\n"

let string_of_type ctxt idx =
  W.string_of_def_type (lookup_def_type ctxt idx)

let string_of_field_type ctxt idx i =
  let idx' = lookup_ref_field_type ctxt idx i in
  Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'

let rec _print_cls ctxt cls =
  let open Printf in
  printf "inst_idx = %ld = %s\n" cls.inst_idx (string_of_type ctxt cls.inst_idx);
  printf "disp_idx = %ld = %s\n" cls.disp_idx (string_of_type ctxt cls.disp_idx);
  printf "cls_idx = %ld = %s\n" cls.cls_idx (string_of_type ctxt cls.cls_idx);
  printf "new : %s\n" (string_of_field_type ctxt cls.cls_idx cls_new);
  printf "pre : %s\n" (string_of_field_type ctxt cls.cls_idx cls_pre_alloc);
  printf "post : %s\n" (string_of_field_type ctxt cls.cls_idx cls_post_alloc);
  printf "inst_flds =";
    List.iter (printf " %s") (List.map W.string_of_field_type cls.inst_flds);
    printf "\n";
  printf "disp_flds =";
    List.iter (printf " %s") (List.map W.string_of_field_type cls.disp_flds);
    printf "\n";
  printf "param_vals =";
    List.iter (printf " %s") (List.map W.string_of_value_type cls.param_vals);
    printf "\n";
  printf "pre_vals =";
    List.iter (fun (x, t) ->
      printf " %s:%s" x (W.string_of_value_type t)) cls.pre_vals;
    printf "\n";
  printf "overrides =";
    List.iter (fun (i, (x, vt)) ->
      printf " %s/%ld:%s" x i (W.string_of_value_type vt)
    ) cls.overrides;
    printf "\n";
  printf "env.vals ="; print_env cls.env;
  if cls.sup = None then printf "sup = none\n%!" else printf "sup =\n";
  Option.iter (_print_cls ctxt) cls.sup


(* Emitter *)

let emit_cls ctxt at id sup : cls * (W.type_ -> W.type_ -> W.type_ -> unit) =
  let inst_idx, r1 = alloc_entity ctxt.types in
  let disp_idx, r2 = alloc_entity ctxt.types in
  let cls_idx, r3 = alloc_entity ctxt.types in
  let cls = make_cls sup inst_idx disp_idx cls_idx in
  ctxt.clss := ClsEnv.add id cls !(ctxt.clss);
  cls,
  fun t1 t2 t3 ->
    define_entity r1 t1; define_entity r2 t2; define_entity r3 t3

let emit_type ctxt at type_ : int32 =
  match DefTypes.find_opt type_ !(ctxt.deftypes) with
  | Some idx -> idx
  | None ->
    let idx = emit_entity ctxt.types (type_ @@ at) in
    ctxt.deftypes := DefTypes.add type_ idx !(ctxt.deftypes);
    idx

let emit_import ctxt at mname name desc =
  let module_name = W.Utf8.decode mname in
  let item_name = W.Utf8.decode name in
  let idesc = desc @@ at in
  ignore (emit_entity ctxt.imports W.({module_name; item_name; idesc} @@ at))

let emit_func_import ctxt at mname name ft =
  let typeidx = emit_type ctxt at W.(FuncDefType ft) in
  emit_import ctxt at mname name W.(FuncImport (typeidx @@ at));
  implicit_entity ctxt.funcs

let emit_global_import ctxt at mname name mut t =
  emit_import ctxt at mname name W.(GlobalImport (GlobalType (t, mut)));
  implicit_entity ctxt.globals

let emit_export descf ctxt at name idx =
  let name = W.Utf8.decode name in
  let edesc = descf (idx @@ at) @@ at in
  ignore (emit_entity ctxt.exports W.({name; edesc} @@ at))

let emit_func_export = emit_export (fun x -> W.FuncExport x)
let emit_global_export = emit_export (fun x -> W.GlobalExport x)

let emit_param ctxt at : int32 =
  implicit_entity ctxt.locals

let emit_local ctxt at t' : int32 =
  emit_entity ctxt.locals (t' @@ at)

let emit_global ctxt at mut t' ginit : int32 =
  let gtype = W.GlobalType (t', mut) in
  emit_entity ctxt.globals (W.{gtype; ginit} @@ at)

let emit_data ctxt at s : int32 =
  let addr = !(ctxt.data_offset) in
  let offset = W.[Const (I32 addr @@ at) @@ at] @@ at in
  let dmode = W.Active {index = 0l @@ at; offset} @@ at in
  let seg = W.{dinit = s; dmode} @@ at in
  ignore (emit_entity ctxt.datas seg);
  ctxt.data_offset := addr +% i32 (String.length s);
  addr

let emit_instr ctxt at instr =
  ignore (emit_entity ctxt.instrs (instr @@ at))

let emit_block ctxt at head bt f =
  let ctxt' = {ctxt with instrs = make_entities ()} in
  f ctxt';
  emit_instr ctxt at (head bt (get_entities ctxt'.instrs))

let emit_let ctxt at bt ts f =
  let ctxt' = {ctxt with instrs = make_entities ()} in
  let _, env = List.hd ctxt.envs in
  let shift = i32 (List.length ts) in
  env := E.map_vals (fun (s, i) ->
    (s, if i >= 0l && (s = T.LetS || s = T.VarS) then i +% shift else i)) !env;
  f ctxt';
  (* Unshift -- can't just restore, since there might be new locals *)
  env := E.map_vals (fun (s, i) ->
    (s, if i >= 0l && (s = T.LetS || s = T.VarS) then i -% shift else i)) !env;
  let locals = List.map (fun t -> t @@ at) ts in
  emit_instr ctxt at (W.let_ bt locals (get_entities ctxt'.instrs))

let emit_func ctxt at ts1' ts2' f : int32 =
  let ft = W.(FuncType (ts1', ts2')) in
  let typeidx = emit_type ctxt at W.(FuncDefType ft) in
  let idx, func = alloc_entity ctxt.funcs in
  let ctxt' = {ctxt with locals = make_entities (); instrs = make_entities ()} in
  f ctxt' idx;
  define_entity func (
    { W.ftype = typeidx @@ at;
      W.locals = get_entities ctxt'.locals;
      W.body = get_entities ctxt'.instrs;
    } @@ at
  );
  idx

let emit_func_ref ctxt at idx =
  ctxt.refs := idx :: !(ctxt.refs)


(* Lowering types *)

let rec lower_value_type ctxt at t : W.value_type =
  match t with
  | T.Bool | T.Byte | T.Int -> W.(NumType I32Type)
  | T.Float -> W.(NumType F64Type)
  | t -> W.(RefType (Nullable, lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match t with
  | T.Var _ -> W.AnyHeapType
  | T.Null -> W.EqHeapType
  | T.Tup [] | T.Bot -> W.AnyHeapType
  | T.Box (T.Bool | T.Byte) -> W.I31HeapType
  | t -> W.(DefHeapType (SynVar (lower_var_type ctxt at t)))

and lower_var_type ctxt at t : int32 =
  match t with
  | T.Obj ->
    emit_type ctxt at W.(StructDefType (StructType []))
  | T.Inst (tcls, ts) ->
    if ts <> [] && not !Flags.parametric then nyi at "generic instance types";
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
  | t -> W.(ValueStorageType (RefType (Nullable, AnyHeapType)))

and lower_field_type ctxt at mut t : W.field_type =
  W.(FieldType (lower_storage_type ctxt at t, mut))

and lower_block_value_type ctxt at t : W.value_type option =
  match t with
  | T.Tup [] -> None
  | t -> Some (lower_value_type ctxt at t)

and lower_block_type ctxt at t : W.block_type =
  W.ValBlockType (lower_block_value_type ctxt at t)

and _lower_block_type2 ctxt at t1 t2 : W.block_type =
  let t1' = lower_value_type ctxt at t1 in
  let t2' = lower_value_type ctxt at t1 in
  W.(VarBlockType (SynVar
    (emit_type ctxt at (FuncDefType (FuncType ([t1'], [t2']))))))

and lower_stack_type ctxt at t : W.value_type list =
  Option.to_list (lower_block_value_type ctxt at t)

and lower_func_type ctxt at t : W.func_type =
  match t with
  | T.Func (ys, ts1, t2) ->
    if ys <> [] && not !Flags.parametric then nyi at "generic functions";
    W.FuncType (
      List.map (lower_value_type ctxt at) ts1,
      lower_stack_type ctxt at t2
    )
  | T.Class tcls ->
    if tcls.T.tparams <> [] && not !Flags.parametric then
      nyi at "generic classes";
    W.FuncType (
      List.map (lower_value_type ctxt at) tcls.T.vparams,
      [lower_value_type ctxt at (T.Inst (tcls, List.map T.var tcls.T.tparams))]
    )
  | _ -> assert false


and lower_class ctxt at tcls =
  match ClsEnv.find_opt tcls.T.id !(ctxt.clss) with Some cls -> cls | None ->

  let (cls, define_cls), sup, tsup_def =
    match tcls.T.sup with
    | T.Obj ->
      emit_cls ctxt at tcls.T.id None, make_cls None (-1l) (-1l) (-1l), []
    | T.Inst (tsup, _) ->
      let sup = lower_class ctxt at tsup in
      emit_cls ctxt at tcls.T.id (Some sup), sup, tsup.T.def
    | _ -> assert false
  in

  let inst_t = T.Inst (tcls, List.map T.var tcls.T.tparams) in
  let inst_vt = lower_value_type ctxt at inst_t in

  let start = i32 (List.length sup.inst_flds + 1) in
  let param_binds =
    List.mapi (fun i t ->
      hidden (i32 i +% start), lower_value_type ctxt at t
    ) tcls.T.vparams
  in
  let param_vts = List.map snd param_binds in
  let param_fts =
    List.map (lower_field_type ctxt at W.Immutable) tcls.T.vparams in

  let clsenv, pre_binds_r, overrides, inst_fts_r, disp_fts_r, _, _ =
    List.fold_left
    (fun (clsenv, pre_binds, ov, inst_fts, disp_fts, inst_i, disp_i) (x, (s, t)) ->
      match E.find_opt_val Source.(x @@ no_region) sup.env with
      | Some si ->
        let ft_idx = lookup_ref_field_type ctxt sup.disp_idx (snd si.it) in
        let vt = lookup_param_type ctxt ft_idx 0 in
        clsenv, pre_binds, (snd si.it, (x, vt))::ov,
        inst_fts, disp_fts, inst_i, disp_i
      | None ->
      match s with
      | T.LetS ->
        let ft = lower_field_type ctxt at W.Immutable t in
        E.extend_val clsenv (Source.(@@) x at) (s, inst_i),
        (x, lower_value_type ctxt at t) :: pre_binds, ov,
        ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
      | T.VarS ->
        let ft = lower_field_type ctxt at W.Mutable t in
        E.extend_val clsenv (Source.(@@) x at) (s, inst_i),
        (hidden 0l, lower_value_type ctxt at t) :: pre_binds, ov,
        ft::inst_fts, disp_fts, inst_i +% 1l, disp_i
      | T.FuncS ->
        let ys, ts1, t2 = T.as_func t in
        let fnt = lower_func_type ctxt at (T.Func (ys, inst_t::ts1, t2)) in
        let idx = emit_type ctxt at W.(FuncDefType (fnt)) in
        let dt = W.(DefHeapType (SynVar idx)) in
        let st = W.(ValueStorageType (RefType (NonNullable, dt))) in
        let ft = W.(FieldType (st, Immutable)) in
        E.extend_val clsenv (Source.(@@) x at) (s, disp_i), pre_binds, ov,
        inst_fts, ft::disp_fts, inst_i, disp_i +% 1l
      | T.ClassS -> nyi at "nested class definitions"
      | T.ProhibitedS -> assert false
    ) (sup.env, [], [], [], [],
        i32 (1 + List.length tcls.T.vparams + List.length sup.inst_flds),
        i32 (List.length sup.disp_flds))
      (W.Lib.List.drop (List.length tsup_def) tcls.T.def)
  in

  let pre_binds = sup.pre_vals @ param_binds @ List.rev pre_binds_r in
  let inst_fts = sup.inst_flds @ param_fts @ List.rev inst_fts_r in
  let disp_fts = sup.disp_flds @ List.rev disp_fts_r in
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
    List.fold_left (fun clsenv (x, _) ->
      E.extend_val clsenv (Source.(@@) x at) (T.LetS, as_hidden x)
    ) clsenv param_binds
  in
  cls.env <- clsenv';
  cls.inst_flds <- inst_fts;
  cls.disp_flds <- disp_fts;
  cls.param_vals <- param_vts;
  cls.pre_vals <- pre_binds;
  cls.overrides <- overrides;
  define_cls (inst_dt @@ at) (disp_dt @@ at) (cls_dt @@ at);
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

let compile_coerce_abs_block_type ctxt at t =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match t with
  | T.Tup [] -> emit ctxt W.[drop]
  | T.Null | T.Bot ->
    emit ctxt W.[drop; ref_null (lower_heap_type ctxt at t)]
  | T.Box (T.Bool | T.Byte) ->
    emit ctxt W.[ref_as_i31]
  | T.Text | T.Box _ | T.Tup _ | T.Obj
  | T.Inst _ | T.Array _ | T.Func _ | T.Class _ ->
    let t' = lower_value_type ctxt at t in
    let tmpidx = emit_local ctxt at W.(RefType (Nullable, AnyHeapType)) in
    let typeidx = lower_var_type ctxt at t in
    emit ctxt W.[
      local_tee (tmpidx @@ at);
      ref_is_null;
      if_ W.(valbt t') [
        ref_null (DefHeapType (SynVar typeidx)) @@ at
      ] [
        local_get (tmpidx @@ at) @@ at;
        ref_as_data @@ at;
        rtt_canon (typeidx @@ at) @@ at;
        ref_cast @@ at;
      ]
    ]
  | _ -> ()


(* Intrinsics *)

let compile_text_new ctxt : int32 =
  match !(ctxt.text_new) with
  | Some idx -> idx
  | None ->
    let at = Prelude.region in
    let typeidx = lower_var_type ctxt at T.Text in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at W.[i32t; i32t] [t'] (fun ctxt idx ->
      ctxt.text_new := Some idx;
      let srcidx = emit_param ctxt at in
      let lenidx = emit_param ctxt at in
      let dstidx = emit_local ctxt at t' in
      List.iter (emit_instr ctxt at) W.[
        local_get (lenidx @@ at);
        rtt_canon (typeidx @@ at);
        array_new_default (typeidx @@ at);
        local_set (dstidx @@ at);
        block voidbt (List.map (fun e -> e @@ at) [
          loop voidbt (List.map (fun e -> e @@ at) [
            local_get (lenidx @@ at);
            i32_eqz;
            br_if (1l @@ at);
            local_get (dstidx @@ at);
            local_get (lenidx @@ at);
            i32_const (1l @@ at);
            i32_sub;
            local_tee (lenidx @@ at);
            local_get (lenidx @@ at);
            local_get (srcidx @@ at);
            i32_add;
            i32_load8_u 0 0l;
            array_set (typeidx @@ at);
            br (0l @@ at);
          ])
        ]);
        local_get (dstidx @@ at);
      ]
    )

let compile_text_cpy ctxt : int32 =
  match !(ctxt.text_cpy) with
  | Some idx -> idx
  | None ->
    let at = Prelude.region in
    let typeidx = lower_var_type ctxt at T.Text in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at W.[t'; i32t; t'; i32t; i32t] [] (fun ctxt idx ->
      ctxt.text_cpy := Some idx;
      let dstidx = emit_param ctxt at in
      let dstkidx = emit_param ctxt at in
      let srcidx = emit_param ctxt at in
      let srckidx = emit_param ctxt at in
      let lenidx = emit_param ctxt at in
      emit_instr ctxt at W.(
        block voidbt (List.map (fun e -> e @@ at) [
          loop voidbt (List.map (fun e -> e @@ at) [
            local_get (lenidx @@ at);
            i32_eqz;
            br_if (1l @@ at);
            local_get (dstidx @@ at);
            local_get (lenidx @@ at);
            i32_const (1l @@ at);
            i32_sub;
            local_tee (lenidx @@ at);
            local_get (dstkidx @@ at);
            i32_add;
            local_get (srcidx @@ at);
            local_get (lenidx @@ at);
            local_get (srckidx @@ at);
            i32_add;
            array_get_u (typeidx @@ at);
            array_set (typeidx @@ at);
            br (0l @@ at);
          ])
        ])
      )
    )

let compile_text_cat ctxt : int32 =
  match !(ctxt.text_cat) with
  | Some idx -> idx
  | None ->
    let text_cpy = compile_text_cpy ctxt in
    let at = Prelude.region in
    let typeidx = lower_var_type ctxt at T.Text in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at [t'; t'] [t'] (fun ctxt idx ->
      ctxt.text_cat := Some idx;
      let arg1idx = emit_param ctxt at in
      let arg2idx = emit_param ctxt at in
      let tmpidx = emit_local ctxt at t' in
      List.iter (emit_instr ctxt at) W.[
        local_get (arg1idx @@ at);
        array_len (typeidx @@ at);
        local_get (arg2idx @@ at);
        array_len (typeidx @@ at);
        i32_add;
        rtt_canon (typeidx @@ at);
        array_new_default (typeidx @@ at);
        local_tee (tmpidx @@ at);
        i32_const (0l @@ at);
        local_get (arg1idx @@ at);
        i32_const (0l @@ at);
        local_get (arg1idx @@ at);
        array_len (typeidx @@ at);
        call (text_cpy @@ at);
        local_get (tmpidx @@ at);
        local_get (arg1idx @@ at);
        array_len (typeidx @@ at);
        local_get (arg2idx @@ at);
        i32_const (0l @@ at);
        local_get (arg2idx @@ at);
        array_len (typeidx @@ at);
        call (text_cpy @@ at);
        local_get (tmpidx @@ at);
      ]
    )

let compile_text_cmp ctxt : int32 =
  match !(ctxt.text_cmp) with
  | Some idx -> idx
  | None ->
    let at = Prelude.region in
    let typeidx = lower_var_type ctxt at T.Text in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at [t'; t'] W.[i32t] (fun ctxt idx ->
      ctxt.text_cmp := Some idx;
      let arg1idx = emit_param ctxt at in
      let arg2idx = emit_param ctxt at in
      let lenidx = emit_local ctxt at W.i32t in
      List.iter (emit_instr ctxt at) W.[
        block voidbt (List.map (fun e -> e @@ at) [
          local_get (arg1idx @@ at);
          local_get (arg2idx @@ at);
          ref_eq;
          if_ voidbt (List.map (fun e -> e @@ at) [
            i32_const (1l @@ at); return
          ]) [];
          local_get (arg1idx @@ at);
          array_len (typeidx @@ at);
          local_get (arg2idx @@ at);
          array_len (typeidx @@ at);
          local_tee (lenidx @@ at);
          i32_ne;
          br_if (0l @@ at);
          block voidbt (List.map (fun e -> e @@ at) [
            loop voidbt (List.map (fun e -> e @@ at) [
              local_get (lenidx @@ at);
              i32_eqz;
              br_if (1l @@ at);
              local_get (arg1idx @@ at);
              local_get (lenidx @@ at);
              i32_const (1l @@ at);
              i32_sub;
              local_tee (lenidx @@ at);
              array_get_u (typeidx @@ at);
              local_get (arg2idx @@ at);
              local_get (lenidx @@ at);
              array_get_u (typeidx @@ at);
              i32_eq;
              br_if (0l @@ at);
            ])
          ]);
          i32_const (1l @@ at);
          return;
        ]);
        i32_const (0l @@ at);
      ]
    )


(* Expressions *)

let compile_lit ctxt l at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match l with
  | NullLit -> emit ctxt W.[ref_null (lower_heap_type ctxt at T.Null)]
  | BoolLit b -> emit ctxt W.[i32_const ((if b then 1l else 0l) @@ at)]
  | IntLit i -> emit ctxt W.[i32_const (i @@ at)]
  | FloatLit z -> emit ctxt W.[f64_const (W.F64.of_float z @@ at)]
  | TextLit s ->
    let addr = emit_data ctxt at s in
    emit ctxt W.[
      i32_const (addr @@ at);
      i32_const (i32 (String.length s) @@ at);
      call (compile_text_new ctxt @@ at);
    ]


let rec find_var ctxt x envs : scope * T.sort * int32 =
  match envs with
  | [] ->
    Printf.printf "[find_var `%s` @@ %s]\n%!" x.it (Source.string_of_region x.at);
    assert false
  | (scope, env)::envs' ->
    match E.find_opt_val x !env with
    | None ->
      let (scope', _, _) as result = find_var ctxt x envs' in
      (match scope', scope with
      | (PreScope | GlobalScope), _
      | (FuncScope | BlockScope), BlockScope
      | ClassScope _, (FuncScope | BlockScope) -> ()
      | _ -> nyi x.at "outer scope variable access"
      );
      result
    | Some {it = (s, idx); _} ->
      assert (match scope with ClassScope _ -> true | _ -> idx >= 0l);
      scope, s, idx

let rec compile_var ctxt x t =
  let scope, s, idx = find_var ctxt x ctxt.envs in
  if s <> T.LetS && s <> T.VarS && s <> T.ClassS then nyi x.at "closures";
  (match scope with
  | PreScope ->
    let _, l = List.nth Prelude.vals (Int32.to_int idx) in
    compile_lit ctxt l x.at
  | BlockScope | FuncScope ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | GlobalScope ->
    emit_instr ctxt x.at W.(global_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | ClassScope _ when idx >= 0l ->  (* in constructor, we have let binding *)
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
    compile_coerce_block_type ctxt x.at t
  | ClassScope this_t ->
    let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
    this.et <- Some this_t;
    let x' = if idx <= -2l then Source.(hidden (-2l -% idx) @@ x.at) else x in
    compile_exp ctxt {it = DotE (this, x'); at = x.at; et = Some t}
  )

and compile_exp ctxt e =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE x ->
    compile_var ctxt x (Source.et e)

  | LitE l ->
    compile_lit ctxt l e.at

  | UnE (op, e1) ->
    (match op, Source.et e with
    | NegOp, T.Int -> emit ctxt W.[i32_const (0l @@ e.at)]
    | InvOp, T.Int -> emit ctxt W.[i32_const (-1l @@ e.at)]
    | _ -> ()
    );
    compile_exp ctxt e1;
    (match op, Source.et e with
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
    (match op, Source.et e with
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
    | AddOp, T.Text -> emit ctxt W.[call (compile_text_cat ctxt @@ e.at)]
    | _ -> assert false
    )

  | RelE (e1, op, e2) ->
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    (match op, T.lub (Source.et e1) (Source.et e2) with
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
    | EqOp, T.Text -> emit ctxt W.[call (compile_text_cmp ctxt @@ e.at)]
    | NeOp, T.Text -> emit ctxt W.[call (compile_text_cmp ctxt @@ e.at); i32_eqz]
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
    (match Source.et e1 with
    | T.Bool | T.Byte ->
      emit ctxt W.[i31_new]
    | _ ->
      let typeidx = lower_var_type ctxt e.at (Source.et e) in
      compile_coerce_value_type ctxt e1.at (Source.et e1);
      emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)]
    )

  | UnboxE e1 ->
    compile_exp ctxt e1;
    (match Source.et e with
    | T.Bool | T.Byte ->
      emit ctxt W.[i31_get_u]
    | _ ->
      let typeidx = lower_var_type ctxt e.at (Source.et e1) in
      let struct_get_sxopt =
        match Source.et e with
        | T.Bool | T.Byte -> W.struct_get_u
        | _ -> W.struct_get
      in
      emit ctxt [struct_get_sxopt (typeidx @@ e.at) (0l @@ e.at)];
      compile_coerce_block_type ctxt e.at (Source.et e)
    )

  | TupE [] ->
    ()

  | TupE es ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    List.iter (fun eI ->
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (Source.et eI);
    ) es;
    emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)]

  | ProjE (e1, n) ->
    let typeidx = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1;
    let struct_get_sxopt =
      match Source.et e with
      | T.Bool | T.Byte -> W.struct_get_u
      | _ -> W.struct_get
    in
    emit ctxt [struct_get_sxopt (typeidx @@ e.at) (i32 n @@ e.at)];
    compile_coerce_abs_block_type ctxt e.at (Source.et e)

  | ArrayE es ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
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
      compile_coerce_value_type ctxt eI.at (Source.et eI);
      emit ctxt W.[array_set (typeidx @@ e.at)];
    ) es

  | LenE e1 ->
    let typeidx = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1;
    emit ctxt W.[array_len (typeidx @@ e.at)]

  | IdxE (e1, e2) ->
    let typeidx = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    let array_get_sxopt =
      match Source.et e with
      | T.Bool | T.Byte -> W.array_get_u
      | _ -> W.array_get
    in
    emit ctxt [array_get_sxopt (typeidx @@ e.at)];
    compile_coerce_abs_block_type ctxt e.at (Source.et e)

  | CallE (e1, ts, es) ->
    if ts <> [] && not !Flags.parametric then nyi e.at "generic function calls";
    let t1 =
      match e1.it with
      | VarE x ->
        let scope, s, idx = find_var ctxt x ctxt.envs in
        (match scope, s with
        | PreScope, _ -> assert false
        | GlobalScope, T.FuncS ->
          List.iter (fun eI ->
            compile_exp ctxt eI;
            compile_coerce_value_type ctxt eI.at (Source.et eI);
          ) es;
          emit ctxt W.[call (idx @@ x.at)]
        | ClassScope this_t, T.FuncS ->
          let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
          this.et <- Some this_t;
          compile_exp ctxt
            {e with it = CallE ({e1 with it = DotE (this, x)}, ts, es)}
        | _, T.FuncS -> nyi x.at "local function calls"
        | _ -> nyi e.at "indirect function calls"
        );
        Source.et e1

      | DotE (e11, x) ->
        let t11 = Source.et e11 in
        let cls = lower_class ctxt e11.at (fst (T.as_inst t11)) in
        let s, idx = (E.find_val x cls.env).it in
        let tmpidx = emit_local ctxt e11.at (lower_value_type ctxt e11.at t11) in
        compile_exp ctxt e11;
        emit ctxt W.[local_tee (tmpidx @@ e.at)];
        List.iter (fun eI ->
          compile_exp ctxt eI;
          compile_coerce_value_type ctxt eI.at (Source.et eI);
        ) es;
        (match s with
        | T.FuncS ->
          emit ctxt W.[
            local_get (tmpidx @@ e11.at);
            struct_get (cls.inst_idx @@ e11.at) (0l @@ x.at);
            struct_get (cls.disp_idx @@ e11.at) (idx @@ x.at);
            call_ref;
          ];
        | T.LetS | T.VarS -> nyi e.at "indirect function calls"
        | T.ClassS -> nyi e.at "nested classes"
        | T.ProhibitedS -> assert false
        );
        let tcls, _ = T.as_inst (Source.et e11) in
        snd (List.assoc x.it tcls.T.def)

      | _ -> nyi e.at "indirect function calls"
    in
    (* TODO: this isn't enough once we have closures or nested classes *)
    let _, _, t = T.as_func t1 in
    if T.is_var t then
      compile_coerce_abs_block_type ctxt e.at (Source.et e)

  | NewE (x, ts, es) ->
    if ts <> [] && not !Flags.parametric then
      nyi e.at "generic object construction";
    let tcls, _ = T.as_inst (Source.et e) in
    let cls = lower_class ctxt e.at tcls in
    List.iter (fun eI ->
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (Source.et eI);
    ) es;
    compile_var ctxt x (T.Class tcls);
    emit ctxt W.[
      struct_get (cls.cls_idx @@ x.at) (cls_new @@ x.at);
      call_ref;
    ];

  | NewArrayE (_t, e1, e2) ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    let t' = lower_value_type ctxt e1.at (Source.et e1) in
    let tmpidx = emit_local ctxt e1.at t' in
    compile_exp ctxt e1;
    emit ctxt W.[local_set (tmpidx @@ e1.at)];
    compile_exp ctxt e2;
    compile_coerce_value_type ctxt e2.at (Source.et e2);
    emit ctxt W.[
      local_get (tmpidx @@ e1.at);
      rtt_canon (typeidx @@ e.at);
      array_new (typeidx @@ e.at);
    ]

  | DotE (e1, x) ->
    let t1 = Source.et e1 in
    let cls = lower_class ctxt e1.at (fst (T.as_inst t1)) in
    let s, idx = (E.find_val x cls.env).it in
    compile_exp ctxt e1;
    (match s with
    | T.LetS | T.VarS ->
      let struct_get_sxopt =
        match Source.et e with
        | T.Bool | T.Byte -> W.struct_get_u
        | _ -> W.struct_get
      in
      emit ctxt [struct_get_sxopt (cls.inst_idx @@ e1.at) (idx @@ x.at)];
      compile_coerce_abs_block_type ctxt e.at (Source.et e)
    | T.FuncS -> nyi e.at "closures"
    | T.ClassS -> nyi e.at "nested classes"
    | T.ProhibitedS -> assert false
    )

  | AssignE (e1, e2) ->
    (match e1.it with
    | VarE x ->
      let scope, s, idx = find_var ctxt x ctxt.envs in
      (match scope with
      | PreScope -> assert false
      | BlockScope | FuncScope ->
        compile_exp ctxt e2;
        compile_coerce_value_type ctxt e2.at (Source.et e2);
        emit_instr ctxt x.at W.(local_set (idx @@ x.at))
      | GlobalScope ->
        compile_exp ctxt e2;
        compile_coerce_value_type ctxt e2.at (Source.et e2);
        emit_instr ctxt x.at W.(global_set (idx @@ x.at))
      | ClassScope this_t ->
        let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
        this.et <- Some this_t;
        compile_exp ctxt
          {e with it = AssignE ({e1 with it = DotE (this, x)}, e2)}
      )

    | IdxE (e11, e12) ->
      let typeidx = lower_var_type ctxt e11.at (Source.et e11) in
      compile_exp ctxt e11;
      compile_exp ctxt e12;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (Source.et e2);
      emit ctxt W.[array_set (typeidx @@ e.at)]

    | DotE (e11, x) ->
      let t11 = Source.et e11 in
      let cls = lower_class ctxt e1.at (fst (T.as_inst t11)) in
      let s, idx = (E.find_val x cls.env).it in
      assert (s = T.VarS);
      compile_exp ctxt e11;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (Source.et e2);
      emit ctxt W.[struct_set (cls.inst_idx @@ e11.at) (idx @@ x.at)]

    | _ -> assert false
    )

  | AnnotE (e1, _t) ->
    compile_exp ctxt e1

  | CastE (e1, t) ->
    nyi e.at "casts"
  (*
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> V.Null
    | V.Obj (t', _) when T.sub t' (eval_typ env t) -> v1
    | V.Obj _ -> V.Null
    | _ -> crash e.at "runtime type error at cast"
    )
  *)

  | AssertE e1 ->
    compile_exp ctxt e1;
    emit ctxt W.[i32_eqz; if_ W.voidbt [unreachable @@ e.at] []]

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at (Source.et e) in
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

  | RetE e ->
    compile_exp ctxt e;
    emit ctxt W.[return]

  | BlockE ds ->
    compile_block ctxt BlockScope ds


(* Declarations *)

and compile_dec pass ctxt d =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
  let scope, env = List.hd ctxt.envs in
  match d.it with
  | ExpD _ when pass = FuncPass || pass = LetPass ->
    ()

  | ExpD e ->
    compile_exp ctxt e

  | LetD (x, _e) when pass = FuncPass || pass = VarPass ->
    env := E.extend_val !env x (T.LetS, -1l)

  | LetD (x, e) ->
    let t = List.hd (snd (Source.et d)) in
    let t' = lower_value_type ctxt x.at t in
    compile_exp ctxt e;
    compile_coerce_value_type ctxt e.at t;
    let idx =
      match scope with
      | PreScope -> assert false

      | BlockScope | FuncScope ->
        assert (pass = FullPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_set (idx @@ d.at)];
        idx

      | GlobalScope ->
        assert (pass = FullPass);
        let const = default_const ctxt x.at t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        emit ctxt W.[global_set (idx @@ d.at)];
        idx

      | ClassScope _ ->
        assert (pass = LetPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_tee (idx @@ d.at)];
        idx
    in
    env := E.extend_val !env x (T.LetS, idx)

  | VarD (x, _, _e) when pass = LetPass ->
    emit ctxt (default_exp ctxt x.at (List.hd (snd (Source.et d))))

  | VarD (x, _, _e) when pass = FuncPass ->
    env := E.extend_val !env x (T.VarS, -1l)

  | VarD (x, _, e) ->
    let t = List.hd (snd (Source.et d)) in
    let t' = lower_value_type ctxt x.at t in
    let idx =
      match scope with
      | PreScope -> assert false

      | BlockScope | FuncScope ->
        assert (pass = FullPass);
        let idx = emit_local ctxt x.at t' in
        compile_exp ctxt e;
        compile_coerce_value_type ctxt e.at t;
        emit ctxt W.[local_set (idx @@ d.at)];
        idx

      | GlobalScope ->
        assert (pass = FullPass);
        let const = default_const ctxt x.at t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        compile_exp ctxt e;
        compile_coerce_value_type ctxt e.at t;
        emit ctxt W.[global_set (idx @@ d.at)];
        idx

      | ClassScope this_t ->
        assert (pass = VarPass);
        let this = Source.(VarE ("this" @@ x.at) @@ x.at) in
        let dot = Source.(DotE (this, x) @@ x.at) in
        let assign = Source.(AssignE (dot, e) @@ d.at) in
        this.et <- Some this_t;
        dot.et <- Some t;
        assign.et <- Some (fst (Source.et d));
        compile_exp ctxt assign;
        -1l
    in
    env := E.extend_val !env x (T.VarS, idx)

  | TypD _ ->
    ()

  | FuncD _ when pass = LetPass ->
    ()

  | FuncD (x, _ys, _xts, _t, _e) when pass = VarPass ->
    env := E.extend_val !env x (T.FuncS, -1l)

  | FuncD (x, ys, xts, _t, e) ->
    if ys <> [] && not !Flags.parametric then
      nyi d.at "generic function definitions";
    let t = List.hd (snd (Source.et d)) in
    let W.FuncType (ts1, ts2) = lower_func_type ctxt d.at t in
    let ts1', cast_opt =
      if pass <> FuncPass then ts1, None else
      let tcls = Option.get ctxt.tcls in
      let cls = lower_class ctxt x.at tcls in
      let this_t = W.(RefType (Nullable, DefHeapType (SynVar cls.inst_idx))) in
      let this_param_t, cast_opt =
        match List.find_opt (fun (_, (x', _)) -> x' = x.it) cls.overrides with
        | Some (_, (_, vt)) -> vt, Some (tcls, cls, this_t)
        | None -> this_t, None
      in this_param_t::ts1, cast_opt
    in
    ignore (emit_func ctxt d.at ts1' ts2
      (fun ctxt idx ->
        let _, env' = List.hd ctxt.envs in
        env' := E.extend_val !env' x (T.FuncS, idx);
        let ctxt = enter_scope ctxt FuncScope in
        let _, env = List.hd ctxt.envs in
        if pass = FuncPass then begin
          let this_param = emit_param ctxt x.at in
          let this =
            match cast_opt with
            | None -> this_param
            | Some (tcls, cls, this_t) ->
              let this = emit_local ctxt x.at this_t in
              emit ctxt W.[
                local_get (this_param @@ x.at);
              ];
              compile_var ctxt Source.(ctxt.self @@ x.at) (T.Class tcls);
              emit ctxt W.[
                struct_get (cls.cls_idx @@ x.at) (cls_rtt @@ x.at);
                ref_cast;
                local_set (this @@ x.at);
              ];
              this
          in env := E.extend_val !env Source.("this" @@ x.at) (T.LetS, this)
        end;
        List.iter (fun (x, _) ->
          let idx = emit_param ctxt x.at in
          env := E.extend_val !env x (T.LetS, idx)
        ) xts;
        compile_exp ctxt e
      )
    )

  | ClassD _ when pass <> FullPass ->
    nyi d.at "nested class definitions"

  | ClassD (x, ys, xts, sup_opt, ds) ->
    if ys <> [] && not !Flags.parametric then
      nyi d.at "generic class definitions";
    let tcls = T.as_class (List.hd (snd (Source.et d))) in
    let cls = lower_class ctxt d.at tcls in
    let cls_ht = W.(DefHeapType (SynVar cls.cls_idx)) in
    let cls_vt = W.(RefType (Nullable, cls_ht)) in
    let inst_t = T.Inst (tcls, List.map T.var tcls.T.tparams) in
    let inst_vt = lower_value_type ctxt d.at inst_t in

    (* Allocate target variable *)
    let idx =
      match scope with
      | BlockScope | FuncScope -> emit_local ctxt x.at cls_vt
      | GlobalScope ->
        let const = W.[ref_null cls_ht @@ d.at] @@ d.at in
        emit_global ctxt x.at W.Mutable cls_vt const
      | ClassScope _ -> nyi d.at "nested class definitions"
      | PreScope -> assert false
    in
    env := E.extend_val !env x (T.ClassS, idx);

    (* Set up scope environment *)
    let ctxt = enter_scope ctxt (ClassScope inst_t) in
    let _, env = List.hd ctxt.envs in

    (* In methods, class parameters are mapped to hidden fields, using an 
     * indirection through a hidden field name. The indirection is indicated via
     * an index <= -2, with the negative difference marking the field index.
     * This matches the set in lower_class.
     *)
    Option.iter (fun sup ->
      env := E.adjoin !env (E.map_vals (fun (s, i) -> (s, -1l)) sup.env);
    ) cls.sup;
    let own_start =
      match cls.sup with
      | None -> 1
      | Some sup -> List.length sup.inst_flds + 1
    in
    List.iteri (fun i (x, _) ->
      let i' = i32 (own_start + i) in
      env := E.extend_val !env Source.(hidden i' @@ x.at) (T.LetS, i');
      env := E.extend_val !env x (T.LetS, -2l -% i');
    ) xts;

    let save_env = !env in

    (* Compile own functions *)
    let ctxt = {ctxt with self = x.it; tcls = Some tcls} in
    compile_decs FuncPass ctxt ds;
    let func_env = !env in
    env := save_env;

    (* Construct dispatch table *)
    (* First, bind and push parent functions, or overrides *)
    let suptmp, sup_at, sup_cls, sup_t, sup_vt =
      match sup_opt with
      | None -> -1l, no_region, cls, T.Bot, W.i32t
      | Some sup ->
        let (x2, _, _) = sup.it in
        let sup_cls = lower_class ctxt x2.at (Source.et sup) in
        let sup_t = T.Class (Source.et sup) in
        let sup_ht = W.(DefHeapType (SynVar sup_cls.cls_idx)) in
        let sup_vt = W.(RefType (Nullable, sup_ht)) in

        (* Load class *)
        let suptmp = emit_local ctxt x2.at sup_vt in
        compile_var ctxt x2 sup_t;

        (* Push all functions from dispatch table *)
        if sup_cls.disp_flds = [] then
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
            match List.assoc_opt (i32 i) cls.overrides with
            | None ->
              emit ctxt W.[
                local_get (disptmp @@ x2.at);
                struct_get (sup_cls.disp_idx @@ x2.at) (i32 i @@ x2.at);
              ];
            | Some (x, _) ->
              let _, i' = (E.find_val Source.(x @@ x2.at) func_env).it in
              emit_func_ref ctxt d.at i';
              emit ctxt W.[ref_func (i' @@ d.at)]
          ) sup_cls.disp_flds
        end;
        suptmp, x2.at, sup_cls, sup_t, sup_vt
    in

    (* Second, push own functions, minus overrides *)
    List.iter (fun (x, si) ->
      match si.it with
      | T.FuncS, i when i >= 0l &&
          not (List.exists (fun (_, (x', _)) -> x = x') cls.overrides) ->
        emit_func_ref ctxt d.at i;
        emit ctxt W.[ref_func (i @@ d.at)]
      | _ -> ()
    ) (E.sorted_vals func_env);

    (* Third, allocate dispatch table (and leave on stack) *)
    emit ctxt W.[
      rtt_canon (cls.disp_idx @@ d.at);
      struct_new (cls.disp_idx @@ d.at);
    ];

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
    let pre_alloc_idx =
      emit_func ctxt d.at cls.param_vals (List.map snd cls.pre_vals)
      (fun ctxt _ ->
        List.iter (fun (x, _) ->
          env := E.extend_val !env x (T.LetS, emit_param ctxt x.at);
        ) xts;

        (* Invoke parent pre-alloc *)
        let sup_pre_vals, sup_at =
          match sup_opt with
          | None -> [], no_region
          | Some sup ->
            let (x2, ts2, es2) = sup.it in
            if ts2 <> [] && not !Flags.parametric then
              nyi x2.at "generic super classes";
            List.iter (compile_exp ctxt) es2;
            compile_var ctxt x sup_t;
            emit ctxt W.[
              struct_get (cls.cls_idx @@ x2.at) (cls_sup @@ x2.at);
              struct_get (sup_cls.cls_idx @@ d.at) (cls_pre_alloc @@ d.at);
              call_ref;
            ];
            sup_cls.pre_vals, sup.at
        in

        (* Return (parent's and) own parameters and let values *)
        (* Bind parent's let values to locals if necessary *)
        let _, sup_let_depth =
          List.fold_right (fun (x, _t) (i, max) ->
            (i + 1, if is_hidden x then max else i)
          ) sup_pre_vals (1, 0)
        in
        if sup_let_depth = 0 then begin
          List.iteri (fun i (x, _) ->
            emit ctxt W.[local_get (i32 i @@ x.at)]
          ) xts;
          compile_decs LetPass ctxt ds;
        end else begin
          let rest_len = List.length sup_pre_vals - sup_let_depth in
          let locals = W.Lib.List.drop rest_len sup_pre_vals in
          let results = W.Lib.List.drop rest_len cls.pre_vals in
          let ft = W.FuncType ([], List.map snd results) in
          let bt = W.(varbt (emit_type ctxt sup_at (FuncDefType ft))) in
          emit_let ctxt sup_at bt (List.map snd locals) (fun ctxt ->
            List.iteri (fun i (x, _) ->
              env := E.extend_val !env Source.(x @@ sup_at) (T.LetS, i32 i);
              emit ctxt W.[local_get (i32 i @@ sup_at)]
            ) locals;
            List.iteri (fun i (x, _) ->
              env := E.extend_val !env x (T.LetS, i32 (i + sup_let_depth));
              emit ctxt W.[local_get (i32 (i + sup_let_depth) @@ x.at)]
            ) xts;
            compile_decs LetPass ctxt ds;
          )
        end;

        env := save_env
      )
    in

    (* Emit post-alloc function *)
    let post_alloc_idx =
      emit_func ctxt d.at [inst_vt] [] (fun ctxt _ ->
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
        env := E.extend_val !env Source.("this" @@ d.at) (T.LetS, this);
        compile_decs VarPass ctxt ds;

        env := save_env
      )
    in

    (* Emit constructor function *)
    let W.FuncType (ts1', ts2') = lower_func_type ctxt d.at (T.Class tcls) in
    let new_idx =
      emit_func ctxt d.at ts1' ts2' (fun ctxt _ ->
        List.iter (fun (x, _) -> ignore (emit_param ctxt x.at)) xts;
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
        List.iteri (fun i (x, _) ->
          emit ctxt W.[local_get (i32 i @@ x.at)]
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
      )
    in

    (* Construct class record (dispatch table is still on stack) *)
    assert (cls_disp = 0l);
    assert (cls_rtt == 1l);
    assert (cls_new == 2l);
    assert (cls_pre_alloc == 3l);
    assert (cls_post_alloc == 4l);
    assert (cls_sup == 5l);
    emit_func_ref ctxt at new_idx;
    emit_func_ref ctxt at pre_alloc_idx;
    emit_func_ref ctxt at post_alloc_idx;
    emit ctxt W.[
      ref_func (new_idx @@ d.at);
      ref_func (pre_alloc_idx @@ d.at);
      ref_func (post_alloc_idx @@ d.at);
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
    if fst (Source.et d) <> T.Tup [] then emit_instr ctxt d.at W.(drop);
    compile_decs pass ctxt ds'


and compile_block ctxt scope ds =
  compile_decs FullPass (enter_scope ctxt scope) ds


(* Programs *)

let compile_imp ctxt d =
  let ImpD (xo, xs, url) = d.it in
  let _, env = List.hd ctxt.envs in
  let x = (match xo with None -> "" | Some x -> x.it ^ "_") in
  List.iter2 (fun xI stat_opt ->
    match stat_opt with
    | None -> ()
    | Some (sort, t) ->
      let x' = Source.((x ^ xI.it) @@ xI.at) in
      let idx =
        match sort with
        | T.LetS | T.VarS ->
          emit_global_import ctxt xI.at url xI.it W.Mutable
            (lower_value_type ctxt xI.at t)
        | T.FuncS ->
          emit_func_import ctxt xI.at url xI.it
            (lower_func_type ctxt xI.at t)
        | T.ClassS ->
          emit_global_import ctxt xI.at url xI.it W.Mutable
            (lower_value_type ctxt xI.at t)
        | T.ProhibitedS -> assert false
      in env := E.extend_val !env x' (sort, idx)
  ) xs (Source.et d)

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let emit ctxt = emit_instr ctxt p.at in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
  List.iter (compile_imp ctxt) is;
  let t' = lower_value_type ctxt p.at (Source.et p) in
  let const = default_const ctxt p.at (Source.et p) in
  let result_idx = emit_global ctxt p.at W.Mutable t' const in
  let start_idx =
    emit_func ctxt p.at [] [] (fun ctxt _ ->
      compile_decs FullPass ctxt ds;
      compile_coerce_value_type ctxt p.at (Source.et p);
      emit ctxt W.(global_set (result_idx @@ p.at));
    )
  in
  emit_global_export ctxt p.at "return" result_idx;
  let _, env = List.hd ctxt.envs in
  E.iter_vals (fun x si ->
    let sort, idx = si.it in
    match sort with
    | T.LetS | T.VarS | T.ClassS -> emit_global_export ctxt si.at x idx
    | T.FuncS -> emit_func_export ctxt si.at x idx
    | T.ProhibitedS -> assert false
  ) !env;
  { W.empty_module with
    W.start = Some (start_idx @@ p.at);
    W.types = get_entities ctxt.types;
    W.globals = get_entities ctxt.globals;
    W.funcs = get_entities ctxt.funcs;
    W.imports = get_entities ctxt.imports;
    W.exports = get_entities ctxt.exports;
    W.datas = get_entities ctxt.datas;
    W.elems =
      if !(ctxt.refs) = [] then [] else W.[
        { etype = (NonNullable, FuncHeapType);
          emode = Declarative @@ p.at;
          einit = List.map (fun idx ->
            [ref_func (idx @@ p.at) @@ p.at] @@ p.at) !(ctxt.refs)
        } @@ p.at
      ];
    W.memories =
      if get_entities ctxt.datas = [] then [] else
      let sz = (!(ctxt.data_offset) +% 0xffffl) /% 0x10000l in
      [{W.mtype = W.(MemoryType {min = sz; max = Some sz})} @@ p.at]
  } @@ p.at
