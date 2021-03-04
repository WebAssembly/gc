open Source
open Syntax

module T = Type
module E = Env

module W =
struct
  include Wasm
  type 'a phrase = 'a Wasm.Source.phrase = {at : Wasm.Source.region; it : 'a}
  include Wasm.Ast
  include Wasm.Types
  include Wasm.Value
  include Wasm.Operators
end

let (@@) = Wasm.Source.(@@)

let _f64 = W.F64.of_float
let i32 = W.I32.of_int_s
let (+%) = Int32.add
let (-%) = Int32.sub
(*
let ( *%) = Int32.mul
*)
let (/%) = Int32.div


exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Compilation context *)

type scope = GlobalScope | BlockScope | FuncScope | ClassScope
type env = (T.sort * int32, int32) E.env

type 'a entities = {mutable list : 'a option ref list; mutable cnt : int32}

type ctxt =
  { types : W.type_ entities;
    globals : W.global entities;
    funcs : W.func entities;
    datas : W.data_segment entities;
    imports : W.import entities;
    exports : W.export entities;
    locals : W.local entities;
    instrs : W.instr entities;
    data_offset : int32 ref;
    envs : (scope * env ref) list;
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


let make_ctxt () =
  { types = make_entities ();
    globals = make_entities ();
    funcs = make_entities ();
    datas = make_entities ();
    imports = make_entities ();
    exports = make_entities ();
    locals = make_entities ();
    instrs = make_entities ();
    data_offset = ref 0l;
    envs = [(GlobalScope, ref E.empty)];
  }

let enter_scope ctxt scope =
  {ctxt with envs = (scope, ref E.empty) :: ctxt.envs}


(* Emitter *)

let emit_type ctxt at type_ : int32 =
  match
    Wasm.Lib.List.index_where (function
      | {contents = Some type_'} -> type_.W.it = type_'.W.it
      | _ -> assert false
    ) ctxt.types.list
  with
  | Some idx -> ctxt.types.cnt -% i32 idx -% 1l
  | None -> emit_entity ctxt.types type_

let emit_export ctxt at name idx descf =
  let edesc = descf (idx @@ at) @@ at in
  ignore (emit_entity ctxt.exports W.({name; edesc} @@ at))

let emit_param ctxt at : int32 =
  let idx = ctxt.locals.cnt in
  ctxt.locals.cnt <- idx +% 1l;
  idx

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

let emit_block ctxt at head t' f =
  let ctxt' = {ctxt with instrs = make_entities ()} in
  f ctxt';
  emit_instr ctxt at (head W.(ValBlockType t') (get_entities ctxt'.instrs))

let emit_func ctxt at ft f : int32 =
  let typeidx = emit_type ctxt at (W.FuncDefType ft @@ at) in
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

let lower_heap_type ctxt at t : W.heap_type =
  match t with
  | T.Var _ | T.Null -> W.AnyHeapType
  | T.Obj -> W.DataHeapType
  | T.Inst _ -> nyi at "instance types"
  | T.Array t -> nyi at "array types"
  | T.Func _ -> nyi at "function types"
  | T.Class _ -> nyi at "class types"
  | _ -> assert false

let lower_value_type ctxt at t : W.value_type =
  match t with
  | T.Bool | T.Byte | T.Int | T.Tup [] | T.Bot -> W.(NumType I32Type)
  | T.Float -> W.(NumType F64Type)
  | T.Text -> nyi at "text types"
  | T.Tup ts -> nyi at "tuple types"
  | t -> W.(RefType (Nullable, lower_heap_type ctxt at t))

let lower_block_type ctxt at t : W.value_type option =
  match t with
  | T.Tup [] -> None
  | t -> Some (lower_value_type ctxt at t)

let default_const ctxt at t : W.const =
  let instr' =
    match t with
    | T.Var _ | T.Null | T.Obj | T.Inst _ | T.Array _ | T.Func _ | T.Class _ ->
      W.(ref_null (lower_heap_type ctxt at t))
    | T.Bool | T.Byte | T.Int | T.Tup [] | T.Bot -> W.(i32_const (0l @@ at))
    | T.Float -> W.(f64_const (W.F64.of_float 0.0 @@ at))
    | T.Text -> nyi at "text results"
    | T.Tup ts -> nyi at "tuple results"
  in [instr' @@ at] @@ at

let compile_coerce ctxt at t1 t2 =
  if T.eq t1 t2 then () else
  match t1, t2 with
  | T.Bot, _ -> ()
  | _, T.Tup [] -> emit_instr ctxt at W.(drop)
  | _ -> nyi at "coercions"


(* Expressions *)

let compile_lit ctxt l at =
  match l with
  | NullLit ->
    emit_instr ctxt at W.(ref_null (lower_heap_type ctxt at T.Null))
  | BoolLit b ->
    emit_instr ctxt at W.(i32_const ((if b then 1l else 0l) @@ at))
  | IntLit i ->
    emit_instr ctxt at W.(i32_const (i @@ at))
  | FloatLit z ->
    emit_instr ctxt at W.(f64_const (W.F64.of_float z @@ at))
  | TextLit t ->
    let _addr = emit_data ctxt at t in
    (* TODO: alloc, copy *)
    nyi at "text literals"


let rec compile_var ctxt x envs =
  match envs with
  | [] -> assert false
  | (scope, env)::envs' ->
    match E.find_opt_val x !env with
    | None ->
      let (scope', _, _) as result = compile_var ctxt x envs' in
      if scope' <> GlobalScope && scope <> BlockScope then
        nyi x.at "outer scope variable access";
      result
    | Some {it = (s, idx); _} -> scope, s, idx


let rec compile_exp ctxt e =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE x ->
    let scope, s, idx = compile_var ctxt x ctxt.envs in
    (match scope with
    | BlockScope | FuncScope ->
      emit_instr ctxt x.at W.(local_get (idx @@ x.at))
    | GlobalScope ->
      emit_instr ctxt x.at W.(global_get (idx @@ x.at))
    | _ -> nyi x.at "local variable access"
    )

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

  | BinE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(Some i32t) (fun ctxt ->
      emit ctxt W.[i32_const (0l @@ e1.at)];
      compile_exp ctxt e1;
      emit ctxt W.[i32_eqz; br_if (0l @@ e.at); drop];
      compile_exp ctxt e2;
    )

  | BinE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(Some i32t) (fun ctxt ->
      emit ctxt W.[i32_const (1l @@ e1.at)];
      compile_exp ctxt e1;
      emit ctxt W.[br_if (0l @@ e.at); drop];
      compile_exp ctxt e2;
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
    | CatOp, T.Text -> nyi e.at "concatenation operator"
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
    | EqOp, T.Text -> nyi e.at "text comparison"
    | NeOp, T.Text -> nyi e.at "text comparison"
    | _ -> assert false
    )

  | TupE [] ->
    ()

  | TupE es ->
    nyi e.at "tuple construction"
  (*
    let vs = List.map (eval_exp env) es in
    V.Tup vs
  *)

  | ProjE (e1, n) ->
    nyi e.at "tuple projection"
  (*
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Tup vs when n < List.length vs -> List.nth vs n
    | _ -> crash e.at "runtime type error at tuple access"
    )
  *)

  | ArrayE es ->
    nyi e.at "array construction"
  (*
    let vs = List.map (eval_exp env) es in
    V.Array (List.map ref vs)
  *)

  | IdxE (e1, e2) ->
    nyi e.at "array indexing"
  (*
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1, v2 with
    | V.Null, _ -> trap e1.at "null reference at array access"
    | V.Array vs, V.Int i when 0l <= i && i < Int32.of_int (List.length vs) ->
      !(List.nth vs (Int32.to_int i))
    | V.Array vs, V.Int i -> trap e.at "array index out of bounds"
    | V.Text t, V.Int i when 0l <= i && i < Int32.of_int (String.length t) ->
      V.Byte t.[Int32.to_int i]
    | V.Text t, V.Int i -> trap e.at "text index out of bounds"
    | _ -> crash e.at "runtime type error at array access"
    )
  *)

  | CallE (e1, ts, es) ->
    if ts <> [] then nyi e.at "generic function calls";
    List.iter (compile_exp ctxt) es;
    (match e1.it with
    | VarE x ->
      let scope, s, idx = compile_var ctxt x ctxt.envs in
      (match scope, s with
      | GlobalScope, T.FuncS ->
        emit ctxt W.[call (idx @@ x.at)]

      | _, T.FuncS -> nyi x.at "local function calls"
      | _ -> nyi e.at "indirect function calls"
      )
    | _ -> nyi e.at "indirect function calls"
    )
  (*
    let v1 = eval_exp env e1 in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap e1.at "null reference at function call"
    | V.Func f -> f (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at function call"
    )
  *)

  | NewE (x, ts, es) ->
    nyi e.at "object construction"
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
    nyi e.at "array construction"
  (*
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1 with
    | V.Int i -> V.Array (List.init (Int32.to_int i) (fun _ -> ref v2))
    | _ -> crash e.at "runtime type error at array instantiation"
    )
  *)

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
      let scope, s, idx = compile_var ctxt x ctxt.envs in
      (match scope with
      | BlockScope | FuncScope ->
        emit_instr ctxt x.at W.(local_set (idx @@ x.at))
      | GlobalScope ->
        emit_instr ctxt x.at W.(global_set (idx @@ x.at))
      | _ -> nyi x.at "local variable assignments"
      )
    | IdxE (e1, e2) ->
      nyi e.at "array assignments"
    (*
      let v1 = eval_exp env e1 in
      let v2 = eval_exp env e2 in
      (match v1, v2 with
      | V.Null, _ -> trap e1.at "null reference at array access"
      | V.Array vs, V.Int i when 0l <= i && i < Wasm.Lib.List32.length vs ->
        Wasm.Lib.List32.nth vs i
      | V.Array vs, V.Int i -> trap e.at "array index out of bounds"
      | _ -> crash e.at "runtime type error at array access"
      )
    *)
    | DotE (e1, x) ->
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
      emit_block ctxt e.at W.block None (fun ctxt ->
        compile_exp ctxt e1;
        emit ctxt W.[i32_eqz; br_if (0l @@ e.at)];
        compile_exp ctxt e2;
        emit ctxt W.[br (1l @@ e.at)];
      );
      compile_exp ctxt e3;
    )

  | WhileE (e1, e2) ->
    emit_block ctxt e.at W.block None (fun ctxt ->
      emit_block ctxt e.at W.loop None (fun ctxt ->
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
    in
    let s = match d.it with VarD _ -> T.VarS | _ -> T.LetS in
    env := E.extend_val !env x (s, idx)

  | TypD (_y, _ys, _t) ->
    ()

  | FuncD (x, ys, xts, t, e) ->
    if ys <> [] then nyi d.at "generic function definitions";
    let ts = List.map (fun (_, t) -> Source.et t) xts in
    let ats = List.map (fun (_, t) -> t.at) xts in
    let ts1' = List.map2 (lower_value_type ctxt) ats ts in
    let t2' = lower_value_type ctxt t.at (Source.et t) in
    ignore (emit_func ctxt d.at W.(FuncType (ts1', [t2'])) (fun ctxt idx ->
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
  (*
    let xs = List.map fst xts in
    let rec f ts vs =
      let env' = E.extend_val env x (T.FuncS, V.Func f) in
      let env' = E.extend_typs_gnd env' ys ts in
      let env' = E.extend_vals_let env' xs vs in
      try eval_exp env' e with Return [v] -> v | Return vs -> V.Tup vs
    in
    V.Tup [], E.singleton_val x (T.FuncS, V.Func f)
  *)

  | ClassD (x, ys, xts, sup_opt, ds) ->
    nyi d.at "class definitions"
  (*
    let ys' = List.map it ys in
    let xs = List.map fst xts in
    let cls =
      if pass <> Post then T.gen_class x.it ys' else
      match eval_exp env (this x) with
      | V.Class (cls, _) -> cls
      | _ -> assert false
    in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x con in
    Option.iter (fun (x2, ts2, _) ->
      let env'' = E.extend_typs_abs env' ys in
      cls.T.sup <- eval_typ env'' (VarT (x2, ts2) @@ x2.at)
    ) sup_opt;
    let rec v_class = V.Class (cls, f)
    and f ts vs =
      let env'' = E.extend_val env' x (T.ClassS, v_class) in
      let env'' = E.extend_typs_gnd env'' ys ts in
      let env'' = E.extend_vals_let env'' xs vs in
      let obj, env''' =
        match sup_opt with
        | None -> ref E.Map.empty, env''
        | Some (x2, ts2, es2) ->
          match eval_exp env'' (NewE (x2, ts2, es2) @@ x2.at) with
          | V.Obj (_, obj') ->
            obj', E.Map.fold (fun x v env ->
              Env.extend_val env (x @@ x2.at) v) !obj' env''
          | v -> crash x2.at "runtime type error at super class instantiation, got %s"
             (V.to_string v)
      in
      let v_inst = V.Obj (con ts, obj) in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x (T.ClassS, v_class) in
      let env''' = E.extend_vals_let env''' xs vs in
      let env''' = E.extend_val_let env''' ("this" @@ x.at) v_inst in
      let _, oenv = eval_block Pre env''' ds in
      obj := E.fold_vals (fun x sv obj ->
        match E.Map.find_opt x obj with
        | None -> E.Map.add x sv.it obj
        | Some (s, v') -> v' := !(snd sv.it); obj
      ) oenv !obj;
      ignore (eval_block Post env''' ds);
      v_inst
    in
    V.Tup [],
    E.adjoin (E.singleton_typ x con) (E.singleton_val x (T.ClassS, v_class))
  *)

  | ImportD (_xs, _url) ->
    nyi d.at "import declarations"

and compile_decs ctxt ds =
  match ds with
  | [] -> ()
  | [d] -> compile_dec ctxt d
  | d::ds' ->
    compile_dec ctxt d;
    compile_coerce ctxt d.at (Source.et d) (T.Tup []);
    compile_decs ctxt ds'


and compile_block ctxt scope ds =
  compile_decs (enter_scope ctxt scope) ds


(* Programs *)

let compile_prog p : W.module_ =
  let Prog ds = p.it in
  let emit ctxt = emit_instr ctxt p.at in
  let ctxt = make_ctxt () in
  let t' = lower_value_type ctxt p.at (Source.et p) in
  let const = default_const ctxt p.at (Source.et p) in
  let result_idx = emit_global ctxt p.at W.Mutable t' const in
  let result_name = W.Utf8.decode "return" in
  emit_export ctxt p.at result_name result_idx (fun x -> W.GlobalExport x);
  let start_idx = emit_func ctxt p.at W.(FuncType ([], [])) (fun ctxt _ ->
    emit ctxt W.(global_get (result_idx @@ p.at));
    compile_decs ctxt ds;
    emit ctxt W.(global_set (result_idx @@ p.at));
    emit ctxt W.(return)
  )
  in
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
