open Source
open Syntax

module T = Type

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


exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Compilation context *)

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
  }

let make_entities () = {list = []; cnt = 0l}
let get_entities ents = List.rev (List.map (fun r -> Option.get !r) ents.list)

let alloc_entity ents : int32 * 'a option ref =
  let idx = ents.cnt in
  let r = ref None in
  ents.cnt <- Int32.add idx 1l;
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
  }


let emit_type ctxt at type_ : int32 =
  match
    Wasm.Lib.List.index_where (function
      | {contents = Some type_'} -> type_.W.it = type_'.W.it
      | _ -> assert false
    ) ctxt.types.list
  with
  | Some idx -> Int32.of_int idx
  | None -> emit_entity ctxt.types type_

let emit_export ctxt at name idx descf =
  let edesc = descf (idx @@ at) @@ at in
  ignore (emit_entity ctxt.exports W.({name; edesc} @@ at))

let emit_global ctxt at gtype ginit : int32 =
  emit_entity ctxt.globals (W.{gtype; ginit} @@ at)

let emit_data ctxt at s : int32 =
  let addr = !(ctxt.data_offset) in
  let offset = W.[Const (I32 addr @@ at) @@ at] @@ at in
  let dmode = W.Active {index = 0l @@ at; offset} @@ at in
  let seg = W.{dinit = s; dmode} @@ at in
  ignore (emit_entity ctxt.datas seg);
  ctxt.data_offset := Int32.(add addr (of_int (String.length s)));
  addr

let emit_instr ctxt at instr =
  ignore (emit_entity ctxt.instrs (instr @@ at))

let emit_func ctxt at f : int32 =
  let idx, func = alloc_entity ctxt.funcs in
  let ctxt' = {ctxt with locals = make_entities (); instrs = make_entities ()} in
  let ft = f ctxt' idx in
  let typeidx = emit_type ctxt at (W.FuncDefType ft @@ at) in
  define_entity func (
    { W.ftype = typeidx @@ at;
      W.locals = get_entities ctxt'.locals;
      W.body = get_entities ctxt'.instrs;
    } @@ at
  );
  idx



(* Mapping types *)

let compile_typ ctxt at t : W.value_type =
  match t with
  | T.Var _ | T.Null -> W.(RefType (Nullable, AnyHeapType))
  | T.Bool | T.Byte | T.Int | T.Tup [] -> W.(NumType I32Type)
  | T.Float -> W.(NumType F64Type)
  | T.Text -> nyi at "text types"
  | T.Obj | T.Inst _ -> W.(RefType (Nullable, DataHeapType))
  | T.Tup ts -> nyi at "tuple types"
  | T.Array t -> nyi at "array types"
  | T.Func _ -> nyi at "function types"
  | T.Class _ -> nyi at "class types"

let default_const ctxt at t : W.const =
  let instr' =
    match t with
    | T.Var _ | T.Null | T.Obj | T.Inst _ | T.Array _ | T.Func _ | T.Class _ ->
      (match compile_typ ctxt at t with
      | W.RefType (_, ht) -> W.(ref_null ht)
      | _ -> assert false
      )
    | T.Bool | T.Byte | T.Int | T.Tup [] -> W.(i32_const (0l @@ at))
    | T.Float -> W.(f64_const (W.F64.of_float 0.0 @@ at))
    | T.Text -> nyi at "text results"
    | T.Tup ts -> nyi at "tuple results"
  in [instr' @@ at] @@ at


(* Expressions *)

let compile_lit ctxt l at =
  match l with
  | NullLit -> ()
  | BoolLit b -> emit_instr ctxt at W.(i32_const ((if b then 1l else 0l) @@ at))
  | IntLit i -> emit_instr ctxt at W.(i32_const (i @@ at))
  | FloatLit z -> emit_instr ctxt at W.(f64_const (W.F64.of_float z @@ at))
  | TextLit t ->
    let _addr = emit_data ctxt at t in
    (* TODO: alloc, copy *)
    nyi at "text literals"


let rec compile_exp ctxt e =
  let emit = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE x -> nyi e.at "variables"
  | LitE l -> compile_lit ctxt l e.at
  | UnE (op, e1) ->
    (match op, Source.et e with
    | NegOp, T.Int -> emit W.[i32_const (0l @@ e.at)]
    | _ -> ()
    );
    compile_exp ctxt e1;
    (match op, Source.et e with
    | PosOp, T.Int -> ()
    | PosOp, T.Float -> ()
    | NegOp, T.Int -> emit W.[i32_sub]
    | NegOp, T.Float -> emit W.[f64_neg]
    | NotOp, T.Bool -> emit W.[i32_eqz]
    | _ -> assert false
    )

  | BinE (e1, AndOp, e2) ->
    compile_exp ctxt e1;
    nyi e.at "conjunction operator"

  | BinE (e1, OrOp, e2) ->
    compile_exp ctxt e1;
    nyi e.at "disjunction operator"

  | BinE (e1, op, e2) ->
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    (match op, Source.et e with
    | AddOp, T.Int -> emit W.[i32_add]
    | SubOp, T.Int -> emit W.[i32_sub]
    | MulOp, T.Int -> emit W.[i32_mul]
    | DivOp, T.Int -> emit W.[i32_div_s]
    | ModOp, T.Int -> emit W.[i32_rem_s]
    | AddOp, T.Float -> emit W.[f64_add]
    | SubOp, T.Float -> emit W.[f64_sub]
    | MulOp, T.Float -> emit W.[f64_mul]
    | DivOp, T.Float -> emit W.[f64_div]
    | CatOp, T.Text -> nyi e.at "concatenation operator"
    | _ -> assert false
    )

  | RelE (e1, op, e2) ->
    compile_exp ctxt e1;
    compile_exp ctxt e2;
    (match op, Source.et e1 with
    | EqOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_eq]
    | NeOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_ne]
    | LtOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_lt_s]
    | GtOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_gt_s]
    | LeOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_le_s]
    | GeOp, (T.Int | T.Byte | T.Bool) -> emit W.[i32_ge_s]
    | EqOp, T.Float -> emit W.[f64_eq]
    | NeOp, T.Float -> emit W.[f64_ne]
    | LtOp, T.Float -> emit W.[f64_lt]
    | GtOp, T.Float -> emit W.[f64_gt]
    | LeOp, T.Float -> emit W.[f64_le]
    | GeOp, T.Float -> emit W.[f64_ge]
    | EqOp, (T.Null | T.Obj | T.Array _ | T.Inst _) -> emit W.[ref_eq]
    | NeOp, (T.Null | T.Obj | T.Array _ | T.Inst _) -> emit W.[ref_eq; i32_eqz]
    | EqOp, T.Text -> nyi e.at "text comparison"
    | NeOp, T.Text -> nyi e.at "text comparison"
    | _ -> assert false
    )

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
    nyi e.at "function calls"
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
    nyi e.at "assignment"
  (*
    let r1 = eval_exp_ref env e1 in
    let v2 = eval_exp env e2 in
    r1 := v2;
    V.Tup []
  *)

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
    emit W.[i32_eqz; if_ (ValBlockType None) [unreachable @@ e.at] []]

  | IfE (e1, e2, e3) ->
    nyi e.at "conditionals"
  (*
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> eval_exp env e2
    | V.Bool false -> eval_exp env e3
    | _ -> crash e.at "runtime type error at conditional"
    )
  *)

  | WhileE (e1, e2) ->
    nyi e.at "loops"
  (*
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> ignore (eval_exp env e2); eval_exp env e
    | V.Bool false -> V.Tup []
    | _ -> crash e.at "runtime type error at loop"
    )
  *)

  | RetE es ->
    nyi e.at "function returns"
  (*
    let vs = List.map (eval_exp env) es in
    raise (Return vs)
  *)

  | BlockE ds ->
    compile_block ctxt ds


(* Declarations *)

and compile_dec ctxt d =
  let _emit = List.iter (emit_instr ctxt d.at) in
  match d.it with
  | ExpD e ->
    compile_exp ctxt e

  | LetD (x, e) ->
    nyi d.at "let definitions"
  (*
    let v = if pass = Post then eval_exp env (this x) else eval_exp env e in
    V.Tup [], E.singleton_val x (T.LetS, v)
  *)

  | VarD (x, t, e) ->
    nyi d.at "variable definitions"
  (*
    let t' = eval_typ env t in
    let v = if pass = Pre then V.default t' else eval_exp env e in
    V.Tup [], E.singleton_val x (T.VarS, v)
  *)

  | TypD (_y, _ys, _t) ->
    ()

  | FuncD (x, ys, xts, _ts, e) ->
    nyi d.at "function definitions"
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
    if (Source.et d <> T.Tup []) then emit_instr ctxt d.at W.(drop);
    compile_decs ctxt ds'


and compile_block ctxt ds =
  compile_decs ctxt ds


(* Programs *)

let compile_prog p : W.module_ =
  let Prog ds = p.it in
  let ctxt = make_ctxt () in
  let t = compile_typ ctxt p.at (Source.et p) in
  let const = default_const ctxt p.at (Source.et p) in
  let result_idx = emit_global ctxt p.at W.(GlobalType (t, Mutable)) const in
  let result_name = W.Utf8.decode "return" in
  emit_export ctxt p.at result_name result_idx (fun x -> W.GlobalExport x);
  let start_idx = emit_func ctxt p.at (fun ctxt _ ->
    let emit = emit_instr ctxt p.at in
    emit W.(global_get (result_idx @@ p.at));
    compile_exp ctxt Source.(BlockE ds @@ no_region);
    emit W.(global_set (result_idx @@ p.at));
    emit W.(return);
    W.FuncType ([], [])
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
      let sz = Int32.(div (add !(ctxt.data_offset) 0xffffl) 0x10000l) in
      [{W.mtype = W.(MemoryType {min = sz; max = Some sz})} @@ p.at]
  } @@ p.at
