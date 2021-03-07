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
(*
let (-%) = Int32.sub
let ( *%) = Int32.mul
*)
let (/%) = Int32.div


(* Failure *)

exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Environment *)

type scope = PreScope | GlobalScope | BlockScope | FuncScope | ClassScope
type env = (T.sort * int32, int32) E.env

let make_env () =
  let env = ref Env.empty in
  List.iteri (fun i (y, _) ->
    env := E.extend_typ !env Source.(y @@ Prelude.region) (i32 i)
  ) Prelude.typs;
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region) (T.LetS, i32 i)
  ) Prelude.vals;
  env


(* Class table *)

module ClsEnv = Map.Make(Int)

type cls =
  { env : env;
    inst_idx : int32;
    disp_idx : int32;
    inst_flds : W.field_type list;
    disp_flds : W.field_type list;
  }

type cls_env = cls ClsEnv.t


(* Compilation context *)

module DefTypes = Map.Make(struct type t = W.def_type let compare = compare end)

type 'a entities = {mutable list : 'a option ref list; mutable cnt : int32}

type ctxt =
  { envs : (scope * env ref) list;
    clss : cls_env ref;
    deftypes : int32 DefTypes.t ref;
    types : W.type_ entities;
    globals : W.global entities;
    funcs : W.func entities;
    datas : W.data_segment entities;
    imports : W.import entities;
    exports : W.export entities;
    locals : W.local entities;
    instrs : W.instr entities;
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
    deftypes = ref DefTypes.empty;
    types = make_entities ();
    globals = make_entities ();
    funcs = make_entities ();
    datas = make_entities ();
    imports = make_entities ();
    exports = make_entities ();
    locals = make_entities ();
    instrs = make_entities ();
    data_offset = ref 0l;
    text_new = ref None;
    text_cat = ref None;
    text_cpy = ref None;
    text_cmp = ref None;
  }

let enter_scope ctxt scope =
  {ctxt with envs = (scope, ref E.empty) :: ctxt.envs}


(* Emitter *)

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
  | T.Inst (cls, ts) ->
    (* TODO: temporary hack to enable empty classes *)
    if ts <> [] || cls.T.tparams <> [] || cls.T.vparams <> []
      || cls.T.sup <> T.Obj || cls.T.def <> Env.Map.empty then
      nyi at "instance types";
    emit_type ctxt at W.(StructDefType (StructType []))
  | T.Text ->
    let ft = W.(FieldType (PackedStorageType Pack8, Mutable)) in
    emit_type ctxt at W.(ArrayDefType (ArrayType ft))
  | T.Box t1 ->
    let ft = W.(FieldType (lower_storage_type ctxt at t1, Immutable)) in
    emit_type ctxt at W.(StructDefType (StructType [ft]))
  | T.Tup ts ->
    let fts = List.map (fun tI ->
      W.(FieldType (lower_storage_type ctxt at tI, Immutable))) ts in
    emit_type ctxt at W.(StructDefType (StructType fts))
  | T.Array t1 -> 
    let ft = W.(FieldType (lower_storage_type ctxt at t1, Mutable)) in
    emit_type ctxt at W.(ArrayDefType (ArrayType ft))
  | T.Func _ -> nyi at "function types"
  | T.Class _ -> nyi at "class types"
  | _ -> assert false

and lower_storage_type ctxt at t : W.storage_type =
  match t with
  | T.Bool | T.Byte -> W.(PackedStorageType Pack8)
  | T.Int | T.Float -> W.(ValueStorageType (lower_value_type ctxt at t))
  | t -> W.(ValueStorageType (RefType (Nullable, AnyHeapType)))

let lower_func_type ctxt at t : W.func_type =
  match t with
  | T.Func (ys, ts1, t2) ->
    if ys <> [] && not !Flags.parametric then nyi at "generic functions";
    W.FuncType (
      List.map (lower_value_type ctxt at) ts1,
      [lower_value_type ctxt at t2]
    )
  | T.Class cls ->
    if cls.T.tparams <> [] && not !Flags.parametric then nyi at "generic classes";
    W.FuncType (
      List.map (lower_value_type ctxt at) cls.T.vparams,
      [lower_value_type ctxt at (T.Inst (cls, List.map T.var cls.T.tparams))]
    )
  | _ -> assert false

let lower_block_value_type ctxt at t : W.value_type option =
  match t with
  | T.Tup [] -> None
  | t -> Some (lower_value_type ctxt at t)

let lower_block_type ctxt at t : W.block_type =
  W.ValBlockType (lower_block_value_type ctxt at t)

let _lower_block_type2 ctxt at t1 t2 : W.block_type =
  let t1' = lower_value_type ctxt at t1 in
  let t2' = lower_value_type ctxt at t1 in
  W.(VarBlockType (SynVar
    (emit_type ctxt at (FuncDefType (FuncType ([t1'], [t2']))))))

let lower_stack_type ctxt at t : W.value_type list =
  Option.to_list (lower_block_value_type ctxt at t)


let default_const ctxt at t : W.const =
  let instr' =
    match t with
    | T.Bool | T.Byte | T.Int -> W.i32_const (0l @@ at)
    | T.Float -> W.f64_const (W.F64.of_float 0.0 @@ at)
    | T.Var _ | T.Null | T.Text | T.Obj | T.Box _ | T.Tup _
    | T.Inst _ | T.Array _ | T.Func _ | T.Class _ | T.Bot ->
      W.ref_null (lower_heap_type ctxt at t)
  in [instr' @@ at] @@ at

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
    emit ctxt W.[
      ref_as_data;  (* TODO: handle null *)
      rtt_canon (lower_var_type ctxt at t @@ at);
      ref_cast;
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


let rec compile_var ctxt x envs =
  match envs with
  | [] -> assert false
  | (scope, env)::envs' ->
    match E.find_opt_val x !env with
    | None ->
      let (scope', _, _) as result = compile_var ctxt x envs' in
      if scope' <> PreScope && scope' <> GlobalScope && scope <> BlockScope then
        nyi x.at "outer scope variable access";
      result
    | Some {it = (s, idx); _} -> scope, s, idx


let rec compile_exp ctxt e =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE x ->
    let scope, s, idx = compile_var ctxt x ctxt.envs in
    if s <> T.LetS && s <> T.VarS then nyi x.at "closures";
    (match scope with
    | BlockScope | FuncScope ->
      emit_instr ctxt x.at W.(local_get (idx @@ x.at))
    | GlobalScope ->
      emit_instr ctxt x.at W.(global_get (idx @@ x.at))
    | PreScope ->
      let _, l = List.nth Prelude.vals (Int32.to_int idx) in
      compile_lit ctxt l e.at
    | _ -> nyi x.at "class scope"
    );
    compile_coerce_block_type ctxt e.at (Source.et e)

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
    (match op, Source.et e1 with
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
    | EqOp, (T.Null | T.Obj | T.Array _ | T.Inst _) -> emit ctxt W.[ref_eq]
    | NeOp, (T.Null | T.Obj | T.Array _ | T.Inst _) -> emit ctxt W.[ref_eq; i32_eqz]
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
    List.iter (fun eI ->
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (Source.et eI);
    ) es;
    (match e1.it with
    | VarE x ->
      let scope, s, idx = compile_var ctxt x ctxt.envs in
      (match scope, s with
      | GlobalScope, T.FuncS ->
        emit ctxt W.[call (idx @@ x.at)]

      | _, T.FuncS -> nyi x.at "local function calls"
      | PreScope, _ -> assert false
      | _ -> nyi e.at "indirect function calls"
      )
    | _ -> nyi e.at "indirect function calls"
    );
    let _, _, t' = T.as_func (Source.et e1) in
    if T.is_var t' then
      compile_coerce_abs_block_type ctxt e.at (Source.et e)

  | NewE (x, ts, es) ->
    (* TODO: temporary hack to enable empty classes *)
    if ts <> [] || es <> [] then nyi e.at "object construction";
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)]
  (*
    let v1 = eval_var env x in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap x.at "null reference at class instantiation"
    | V.Class (_, f) -> f (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at class instantiation"
    )
  *)

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
    nyi e.at "object access"
  (*
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> trap e1.at "null reference at object access"
    | V.Obj (_, obj) ->
      (try !(snd (E.Map.find x.it !obj))
       with _ -> crash e.at "unknown field `%s`" x.it)
    | _ -> crash e.at "runtime type error at object access"
    )
  *)

  | AssignE (e1, e2) ->
    (match e1.it with
    | VarE x ->
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (Source.et e2);
      let scope, s, idx = compile_var ctxt x ctxt.envs in
      (match scope with
      | BlockScope | FuncScope ->
        emit_instr ctxt x.at W.(local_set (idx @@ x.at))
      | GlobalScope ->
        emit_instr ctxt x.at W.(global_set (idx @@ x.at))
      | PreScope -> assert false
      | _ -> nyi x.at "local variable assignments"
      )

    | IdxE (e11, e12) ->
      let typeidx = lower_var_type ctxt e.at (Source.et e11) in
      compile_exp ctxt e11;
      compile_exp ctxt e12;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (Source.et e2);
      emit ctxt W.[array_set (typeidx @@ e.at)]

    | DotE (e11, x) ->
      nyi e.at "object field assignments"
    (*
      let v1 = eval_exp env e1 in
      (match v1 with
      | V.Null -> trap e1.at "null reference at object access"
      | V.Obj (_, obj) ->
        (try snd (E.Map.find x.it !obj)
         with _ -> crash e.at "unknown field `%s`" x.it)
      | _ -> crash e.at "runtime type error at object access"
      )
    *)
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

and compile_dec ctxt d =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
  match d.it with
  | ExpD e ->
    compile_exp ctxt e

  | LetD (x, e) | VarD (x, _, e) ->
    let scope, env = List.hd ctxt.envs in
    let t' = lower_value_type ctxt x.at (Source.et e) in
    compile_exp ctxt e;
    compile_coerce_value_type ctxt e.at (Source.et e);
    let idx =
      match scope with
      | BlockScope | FuncScope ->
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_set (idx @@ d.at)];
        idx

      | GlobalScope ->
        let const = default_const ctxt x.at (Source.et e) in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        emit ctxt W.[global_set (idx @@ d.at)];
        idx

      | ClassScope -> nyi d.at "class field definitions"

      | PreScope -> assert false
    in
    let s = match d.it with VarD _ -> T.VarS | _ -> T.LetS in
    env := E.extend_val !env x (s, idx)

  | TypD (_y, _ys, _t) ->
    ()

  | FuncD (x, ys, xts, t, e) ->
    if ys <> [] && not !Flags.parametric then
      nyi d.at "generic function definitions";
    let ts = List.map (fun (_, t) -> Source.et t) xts in
    let ats = List.map (fun (_, t) -> t.at) xts in
    let ts1' = List.map2 (lower_value_type ctxt) ats ts in
    let ts2' = lower_stack_type ctxt t.at (Source.et t) in
    ignore (emit_func ctxt d.at ts1' ts2' (fun ctxt idx ->
      let _, env' = List.hd ctxt.envs in
      env' := E.extend_val !env' x (T.FuncS, idx);
      let ctxt = enter_scope ctxt FuncScope in
      let _, env = List.hd ctxt.envs in
      List.iter (fun (x, _) ->
        let idx = emit_param ctxt x.at in
        env := E.extend_val !env x (T.LetS, idx)
      ) xts;
      compile_exp ctxt e;
    ))

  | ClassD (x, ys, xts, sup_opt, ds) ->
    (* TODO: temporary hack to enable empty classes *)
    let scope, env = List.hd ctxt.envs in
    if scope <> GlobalScope || ys <> [] || xts <> [] || sup_opt <> None || ds <> [] then
      nyi d.at "class definitions";
    let typeidx = emit_type ctxt d.at W.(StructDefType (StructType [])) in
    let t = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    ignore (emit_func ctxt d.at [] [t] (fun ctxt idx ->
      env := E.extend_val !env x (T.FuncS, idx);
      emit ctxt W.[unreachable]
    ))
  (*
    let ys' = List.map it ys in
    let xs = List.map fst xts in
    let cls =
      if pass <> Post then T.gen_class d x.it ys' else
      match eval_exp env (this x) with
      | V.Class (cls, _, _) -> cls
      | _ -> assert false
    in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x con in
    Option.iter (fun (x2, ts2, _) ->
      let env'' = E.extend_typs_abs env' ys in
      cls.T.sup <- eval_typ env'' (VarT (x2, ts2) @@ x2.at)
    ) sup_opt;
    let rec v_class = V.Class (cls, inst, alloc)
    and inst ts vs =
      let v_inst, init = alloc (con ts) ts vs in
      init (); v_inst
    and alloc t_inst ts vs =
      let env'' = E.extend_val env' x (T.ClassS, v_class) in
      let env'' = E.extend_typs_gnd env'' ys ts in
      let env'' = E.extend_vals_let env'' xs vs in
      let v_inst, init', env''' =
        match sup_opt with
        | None -> V.Obj (t_inst, ref E.Map.empty), (fun () -> ()), env''
        | Some (x2, ts2, es2) ->
          let v2 = eval_var env'' x2 in
          let ts2' = List.map (eval_typ env'') ts2 in
          let vs2 = List.map (eval_exp env'') es2 in
          (match v2 with
          | V.Null -> trap x2.at "null reference at class instantiation"
          | V.Class (_, _, alloc') ->
            let v_inst, init' = alloc' t_inst ts2' vs2 in
            v_inst, init', E.Map.fold (fun x v env ->
              Env.extend_val env (x @@ x2.at) v) !(V.as_obj v_inst) env''
          | _ -> crash x2.at "runtime type error at class instantiation"
          )
      in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x (T.ClassS, v_class) in
      let env''' = E.extend_vals_let env''' xs vs in
      let env''' = E.extend_val_let env''' ("this" @@ x.at) v_inst in
      let _, oenv = eval_block Pre env''' ds in
      let obj = V.as_obj v_inst in
      obj := E.fold_vals (fun x sv obj ->
        match E.Map.find_opt x obj with
        | None -> E.Map.add x sv.it obj
        | Some (s, v') -> v' := !(snd sv.it); obj
      ) oenv !obj;
      v_inst,
      fun () -> init' (); ignore (eval_block Post env''' ds)
    in
    V.Tup [],
    E.adjoin (E.singleton_typ x con) (E.singleton_val x (T.ClassS, v_class))
  *)


and compile_decs ctxt ds =
  match ds with
  | [] -> ()
  | [d] -> compile_dec ctxt d
  | d::ds' ->
    compile_dec ctxt d;
    if Source.et d <> T.Tup [] then emit_instr ctxt d.at W.(drop);
    compile_decs ctxt ds'


and compile_block ctxt scope ds =
  compile_decs (enter_scope ctxt scope) ds


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
        | T.FuncS | T.ClassS ->
          emit_func_import ctxt xI.at url xI.it
            (lower_func_type ctxt xI.at t)
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
      compile_decs ctxt ds;
      compile_coerce_value_type ctxt p.at (Source.et p);
      emit ctxt W.(global_set (result_idx @@ p.at));
    )
  in
  emit_global_export ctxt p.at "return" result_idx;
  let _, env = List.hd ctxt.envs in
  E.iter_vals (fun x si ->
    let sort, idx = si.it in
    match sort with
    | T.LetS | T.VarS -> emit_global_export ctxt si.at x idx
    | T.FuncS | T.ClassS -> emit_func_export ctxt si.at x idx
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
    W.memories =
      if !(ctxt.data_offset) = 0l then [] else
      let sz = (!(ctxt.data_offset) +% 0xffffl) /% 0x10000l in
      [{W.mtype = W.(MemoryType {min = sz; max = Some sz})} @@ p.at]
  } @@ p.at
