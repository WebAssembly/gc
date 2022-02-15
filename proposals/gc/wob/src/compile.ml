open Source
open Syntax
open Emit
open Lower

module T = Type
module E = Env
module W = Emit.W


(* Helpers *)

exception NYI = NYI

let type_of = Source.et
let result_type_of d = fst (type_of d)
let bind_type_of d = snd (type_of d)

let (@@) = W.Source.(@@)


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
  try W.string_of_sub_type (Emit.lookup_sub_type ctxt idx)
  with Invalid_argument _ -> "?"

let string_of_field_type ctxt idx i =
  try
    let idx' = Emit.lookup_ref_field_type ctxt idx i in
    Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'
  with Invalid_argument _ -> "?"

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


(* Intrinsics *)

let intrinsic compile import =
  (if !Flags.headless then compile else import)

let intrinsic_text_new c = intrinsic Intrinsic.compile_text_new Runtime.import_text_new c
let intrinsic_text_cat c = intrinsic Intrinsic.compile_text_cat Runtime.import_text_cat c
let intrinsic_text_eq c = intrinsic Intrinsic.compile_text_eq Runtime.import_text_eq c
let intrinsic_rtt_eq c = intrinsic Intrinsic.compile_rtt_eq Runtime.import_rtt_eq c


(* Allocate data *)

let data_list data_e ctxt es data =
  List.fold_left (fun data eI -> data_e ctxt eI data) data es

let data_lit ctxt l at data =
  match l with
  | NullL | BoolL _ | IntL _ | FloatL _ -> data
  | TextL s ->
    ignore (Runtime.import_mem_alloc ctxt);
    ignore (Runtime.import_text_new ctxt);
    if Env.Map.find_opt s !(ctxt.ext.texts) <> None then data else
    let addr = int32 (String.length data) in
    ctxt.ext.texts := Env.Map.add s addr !(ctxt.ext.texts);
    data ^ s

let rec data_exp ctxt e data =
  match e.it with
  | VarE _ -> data
  | LitE l ->
    data_lit ctxt l e.at data
  | UnE (_, e1) | BoxE e1 | UnboxE e1 | ProjE (e1, _) | LenE e1 | DotE (e1, _)
  | AnnotE (e1, _) | AssertE e1 | RetE e1 ->
    data_exp ctxt e1 data
  | CastE (e1, _, _) ->
    ignore (Runtime.import_rtt_eq ctxt);
    data_exp ctxt e1 data
  | BinE (e1, op, e2) ->
    (match op, type_of e with
    | AddOp, T.Text -> ignore (Runtime.import_text_cat ctxt)
    | _ -> ()
    );
    data_list data_exp ctxt [e1; e2] data
  | RelE (e1, op, e2) ->
    (match op, T.lub (type_of e1) (type_of e2) with
    | (EqOp | NeOp), T.Text -> ignore (Runtime.import_text_eq ctxt)
    | _ -> ()
    );
    data_list data_exp ctxt [e1; e2] data
  | LogE (e1, _, e2)
  | IdxE (e1, e2) | NewArrayE (_, e1, e2) | AssignE (e1, e2) | WhileE (e1, e2) ->
    data_list data_exp ctxt [e1; e2] data
  | TupE es | ArrayE es | NewE (_, _, es) ->
    data_list data_exp ctxt es data
  | CallE (e1, _, es) ->
    data_list data_exp ctxt (e1::es) data
  | IfE (e1, e2, e3) ->
    data_list data_exp ctxt [e1; e2; e3] data
  | BlockE ds ->
    data_list data_dec ctxt ds data

and data_dec ctxt d data =
  match d.it with
  | TypD _ -> data
  | ExpD e | LetD (_, e) | VarD (_, _, e) | FuncD (_, _, _, _, e) ->
    data_exp ctxt e data
  | ClassD (_, _, _, _, ds) ->
    data_list data_dec ctxt ds data

let data_prog ctxt p =
  let Prog (_, ds) = p.it in
  data_list data_dec ctxt ds ""


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
      if_ (result t') [
        ref_null (DefHeapType (SynVar typeidx)) @@ at
      ] (
        [ local_get (tmpidx @@ at) @@ at;
          ref_as_data @@ at;
          rtt_canon (typeidx @@ at) @@ at;
          ref_cast @@ at;
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
    | ArrayT (t1, m) ->
      (match m.it with
      | MutT -> emit ctxt W.[i32_const (9l @@ t.at); i31_new]; [t1]
      | ConstT -> emit ctxt W.[i32_const (10l @@ t.at); i31_new]; [t1]
      )
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
      i32_const (int32 (List.length ts + 1) @@ t.at);
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
        i32_const (int32 (i + 1) @@ tI.at);
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
    if !Flags.headless then begin
      let addr = emit_active_data ctxt at s in
      emit ctxt W.[
        i32_const (addr @@ at);
      ]
    end else if s = "" then begin
      emit ctxt W.[
        i32_const (0l @@ at);
      ]
    end else begin
      let offset = Env.Map.find s !(ctxt.ext.texts) in
      emit ctxt W.[
        global_get (!(ctxt.ext.data) @@ at);
      ];
      if offset <> 0l then begin
        emit ctxt W.[
          i32_const (offset @@ at);
          i32_add;
        ]
      end
    end;
    emit ctxt W.[
      i32_const (int32 (String.length s) @@ at);
      call (intrinsic_text_new ctxt @@ at);
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
      emit ctxt W.[call (intrinsic_text_cat ctxt @@ e.at)]
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
      emit ctxt W.[call (intrinsic_text_eq ctxt @@ e.at)]
    | NeOp, T.Text ->
      emit ctxt W.[call (intrinsic_text_eq ctxt @@ e.at); i32_eqz]
    | _ -> assert false
    )

  | LogE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
      emit ctxt W.[i32_const (0l @@ e1.at)];
      compile_exp ctxt e1;
      emit ctxt W.[i32_eqz; br_if (0l @@ e.at); drop];
      compile_exp ctxt e2;
    )

  | LogE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
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
      compile_coerce_abs_block_type ctxt e.at (type_of e)
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
    emit ctxt [struct_get_sxopt (typeidx @@ e.at) (int32 n @@ e.at)];
    compile_coerce_abs_block_type ctxt e.at (type_of e)

  | ArrayE es ->
    let typeidx = lower_var_type ctxt e.at (type_of e) in
    emit ctxt W.[
      i32_const (int32 (List.length es) @@ e.at);
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
      emit ctxt W.[local_get (tmpidx @@ e.at); i32_const (int32 i @@ e.at)];
      compile_exp ctxt eI;
      compile_coerce_value_type ctxt eI.at (type_of eI);
      emit ctxt W.[array_set (typeidx @@ e.at)];
    ) es

  | LenE e1 ->
    compile_exp ctxt e1;
    emit ctxt W.[array_len]

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
      let t111, _ = T.as_array (type_of e11) in
      let typeidx = lower_var_type ctxt e11.at (type_of e11) in
      compile_exp ctxt e11;
      compile_exp ctxt e12;
      compile_exp ctxt e2;
      compile_coerce_value_type ctxt e2.at (type_of e2);
      compile_coerce_null_type ctxt e2.at (type_of e2) t111;
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
          struct_get (cls.disp_idx @@ x.at) (int32 offset @@ x.at);
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
            struct_get (cls.inst_idx @@ x.at) (int32 (i + start) @@ x.at);
            call (intrinsic_rtt_eq ctxt @@ t.at);
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
      if_ void [unreachable @@ e.at] []
    ]

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at (type_of e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      emit_block ctxt e.at W.block W.void (fun ctxt ->
        compile_exp ctxt e1;
        emit ctxt W.[i32_eqz; br_if (0l @@ e.at)];
        compile_exp ctxt e2;
        emit ctxt W.[br (1l @@ e.at)];
      );
      compile_exp ctxt e3;
    )

  | WhileE (e1, e2) ->
    emit_block ctxt e.at W.block W.void (fun ctxt ->
      emit_block ctxt e.at W.loop W.void (fun ctxt ->
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
      | GlobalScope -> emit_global ctxt x.at W.Mutable cls_vt None
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
        let idx = emit_global ctxt x.at W.Mutable t' None in
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
        let idx = emit_global ctxt x.at W.Mutable t' None in
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
                    local_get (int32 !i @@ x.at);
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
        let i' = int32 (own_start + i) in
        let y' = hidden i' in
        env := E.extend_typ !env Source.(y' @@ x.at) (T.LetS, DirectLoc i');
        env := E.extend_typ !env yI (T.LetS, InstanceLoc y');
      ) ys
    end;
    List.iteri (fun i (xI, _) ->
      let i' = int32 (own_start + offset + i) in
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
      | None -> -1l, no_region, cls, cls_def, T.Bot, W.i32
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
            match List.assoc_opt (int32 i) cls_def.overrides with
            | None ->
              emit ctxt W.[
                local_get (disptmp @@ x2.at);
                struct_get (sup_cls.disp_idx @@ x2.at) (int32 i @@ x2.at);
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
        struct_set (cls.disp_idx @@ d.at) (int32 offset @@ d.at);
        local_get (disptmp @@ d.at);
        ref_as_non_null;
      ]
    end;

    (* Allocate RTT (and leave on stack) *)
    emit ctxt W.[
      rtt_canon (cls.inst_idx @@ d.at);
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
              emit ctxt W.[local_get (int32 i @@ yI.at)]
            ) ys;
          end;
          List.iteri (fun i (x, _) ->
            emit ctxt W.[local_get (int32 (i + offset) @@ x.at)]
          ) xts;
          compile_decs LetPass ctxt ds;
        end else begin
          let rest_len = List.length sup_pre_vals - sup_let_depth in
          let locals = W.Lib.List.drop rest_len sup_pre_vals in
          let results = W.Lib.List.drop rest_len cls_def.pre_vals in
          let bt = W.(typeuse (emit_type ctxt sup_at
            (sub [] (func [] (List.map snd results))))) in
          emit_let ctxt sup_at bt (List.map snd locals) (fun ctxt ->
            List.iteri (fun i (xI, _) ->
              let loc = DirectLoc (int32 i) in
              env := E.extend_val !env Source.(xI @@ sup_at) (T.LetS, loc);
              emit ctxt W.[local_get (int32 i @@ sup_at)]
            ) locals;
            if not !Flags.parametric then begin
              List.iteri (fun i yI ->
                let loc = DirectLoc (int32 (i + sup_let_depth)) in
                env := E.extend_typ !env yI (T.LetS, loc);
                emit ctxt W.[local_get (int32 (i + sup_let_depth) @@ yI.at)]
              ) ys;
            end;
            List.iteri (fun i (xI, _) ->
              let loc = DirectLoc (int32 (i + offset + sup_let_depth)) in
              env := E.extend_val !env xI (T.LetS, loc);
              emit ctxt W.[local_get (int32 (i + offset + sup_let_depth) @@ xI.at)]
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
            emit ctxt W.[local_get (int32 !i @@ yI.at)];
            incr i
          ) ys;
        end;
        List.iter (fun (xI, _) ->
          emit ctxt W.[local_get (int32 !i @@ xI.at)];
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
    assert (cls_rtt = 1l);
    assert (cls_new = 2l);
    assert (cls_pre_alloc = 3l);
    assert (cls_post_alloc = 4l);
    assert (cls_sup = 5l);
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
  let x = (match xo with None -> "" | Some x -> x.it) in
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
  let emit ctxt = List.iter (emit_instr ctxt p.at) in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
  let data = if !Flags.headless then "" else data_prog ctxt p in
  List.iter (compile_imp ctxt) is;
  ctxt_flush ctxt;
  let t' = lower_value_type ctxt p.at (type_of p) in
  let result_idx = emit_global ctxt p.at W.Mutable t' None in
  let start_idx =
    emit_func ctxt p.at [] [] (fun ctxt _ ->
      if data <> "" then begin
        let seg = emit_passive_data ctxt p.at data in
        let len = int32 (String.length data) in
        let dataidx = emit_global ctxt p.at W.Mutable W.i32 None in
        ctxt.ext.data := dataidx;
        emit ctxt W.[
          i32_const (len @@ p.at);
          call (Runtime.import_mem_alloc ctxt @@ p.at);
          global_set (dataidx @@ p.at);
          global_get (dataidx @@ p.at);
          i32_const (0l @@ p.at);
          i32_const (len @@ p.at);
          memory_init (seg @@ p.at);
        ]
      end;
      compile_block ctxt ds;
      compile_coerce_value_type ctxt p.at (type_of p);
      emit ctxt W.[
        global_set (result_idx @@ p.at)
      ];
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
