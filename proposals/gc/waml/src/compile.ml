open Source
open Syntax
open Emit

module T = Type
module E = Env
module W = Emit.W


(* Helpers *)

let (@@) = W.Source.(@@)

let i32 = W.I32.of_int_s
let (+%) = Int32.add


(* Failure *)

exception NYI of Source.region * string

let nyi at s = raise (NYI (at, s))


(* Environment *)

type loc =
  | DirectLoc of int32

type data_con = {tag : int32; typeidx : int32; flds : T.typ list}
type data = (string * data_con) list
type env = (loc, data, loc, unit) E.env
type scope = PreScope | LocalScope | GlobalScope | ModuleScope


let make_env () =
  let env = ref Env.empty in
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region) (DirectLoc (i32 i))
  ) Prelude.vals;
  env

type pass = FullPass


(* Compilation context *)

type ctxt_ext = {envs : (scope * env ref) list}
type ctxt = ctxt_ext Emit.ctxt

let make_ext_ctxt () : ctxt_ext = {envs = [(PreScope, make_env ())]}
let make_ctxt () : ctxt =
  Emit.make_ctxt (make_ext_ctxt ())

let enter_scope ctxt scope : ctxt =
  {ctxt with ext = {envs = (scope, ref E.empty) :: ctxt.ext.envs}}

let current_scope ctxt : scope * env ref =
  List.hd ctxt.ext.envs

(*
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
*)

let rec find_typ_var ctxt y envs : data =
  match envs with
  | [] ->
    Printf.printf "[find_typ_var `%s` @@ %s]\n%!" y.it
      (Source.string_of_region y.at);
    assert false
  | (_, env)::envs' ->
    match E.find_opt_typ y !env with
    | None -> find_typ_var ctxt y envs'
    | Some {it = data; _} -> data


(* Debug printing *)

(*
let string_of_loc = function
  | DirectLoc i -> Int32.to_string i

let print_env env =
  E.iter_vals (fun x sl -> let s, l = sl.it in
    Printf.printf " %s(%s)=%s" (string_of_sort s) x (string_of_loc l)) env;
  Printf.printf "\n"

let string_of_type ctxt idx =
  W.string_of_def_type (Emit.lookup_def_type ctxt idx)

let string_of_field_type ctxt idx i =
  let idx' = Emit.lookup_ref_field_type ctxt idx i in
  Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'
*)


(* Lowering types *)

type rep =
  | DropRep         (* value never used *)
  | BlockRep        (* like Boxed, but empty tuples are suppressed *)
  | BoxedRep        (* representation that is compatible with anyref *)
  | UnboxedLaxRep   (* like UnboxedRigid, but Int may have junk high bit *)
  | UnboxedRigidRep (* representation with unboxed type or concrete ref types *)

let pat_rep = BoxedRep

let scope_rep = function
  | PreScope -> UnboxedRigidRep
  | LocalScope | ModuleScope | GlobalScope -> BoxedRep

let is_boxed_rep = function
  | BlockRep | BoxedRep -> true
  | _ -> false

let rec lower_value_type ctxt at rep t : W.value_type =
  if is_boxed_rep rep then W.(RefType (Nullable, EqHeapType)) else
  match T.norm t with
  | T.Bool | T.Byte | T.Int -> W.(NumType I32Type)
  | T.Float -> W.(NumType F64Type)
  | t -> W.(RefType (Nullable, lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match T.norm t with
  | T.Var _ -> W.EqHeapType
  | T.Bool | T.Byte | T.Int -> W.I31HeapType
  | T.Tup [] -> W.EqHeapType
  | t -> W.(DefHeapType (SynVar (lower_var_type ctxt at t)))

and lower_var_type ctxt at t : int32 =
  match T.norm t with
  | T.Float ->
    let ft = W.(FieldType (ValueStorageType (NumType F64Type), Immutable)) in
    emit_type ctxt at W.(StructDefType (StructType [ft]))
  | T.Text ->
    let ft = W.(FieldType (PackedStorageType Pack8, Mutable)) in
    emit_type ctxt at W.(ArrayDefType (ArrayType ft))
  | T.Tup ts ->
    let fts = List.map (lower_field_type ctxt at W.Immutable BoxedRep) ts in
    emit_type ctxt at W.(StructDefType (StructType fts))
  | T.Ref t1 ->
    let ft = lower_field_type ctxt at W.Mutable BoxedRep t1 in
    emit_type ctxt at W.(StructDefType (StructType [ft]))
  | T.Fun _ -> nyi at "function types"
  | _ -> Printf.printf "%s\n%!" (T.string_of_typ t); assert false

and lower_storage_type ctxt at rep t : W.storage_type =
  W.(ValueStorageType (lower_value_type ctxt at rep t))

and lower_field_type ctxt at mut rep t : W.field_type =
  W.(FieldType (lower_storage_type ctxt at rep t, mut))

and lower_block_type ctxt at rep t : W.block_type =
  match t with
  | T.Tup [] when rep = BlockRep -> W.ValBlockType None
  | t -> W.ValBlockType (Some (lower_value_type ctxt at rep t))

(*
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
*)


(* Coercions *)

let default_exp ctxt at rep t : W.instr' list =
  if is_boxed_rep rep then W.[ref_null (lower_heap_type ctxt at t)] else
  match T.norm t with
  | T.Bool | T.Byte | T.Int -> W.[i32_const (0l @@ at)]
  | T.Float -> W.[f64_const (W.F64.of_float 0.0 @@ at)]
  | T.Var _ | T.Text | T.Tup _ | T.Ref _ | T.Fun _ ->
    W.[ref_null (lower_heap_type ctxt at t)]
  | T.Infer _ -> assert false

let default_const ctxt at rep t : W.const =
  List.map (fun instr' -> instr' @@ at) (default_exp ctxt at rep t) @@ at


let compile_coerce ctxt src dst t at =
  if src <> dst then
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match src, dst with
  | BlockRep, DropRep when T.eq t (T.Tup []) ->
    ()
  | _, DropRep ->
    emit ctxt W.[drop]
  | _, BlockRep when T.eq t (T.Tup []) ->
    emit ctxt W.[drop]
  | BlockRep, _ when T.eq t (T.Tup []) ->
    emit_instr ctxt at (W.ref_null (lower_heap_type ctxt at (T.Tup [])))
  | BoxedRep, BlockRep
  | BlockRep, BoxedRep ->
    ()
  | UnboxedLaxRep, UnboxedRigidRep when T.eq t T.Int ->
    emit ctxt W.[
      i32_const (1l @@ at); i32_shl;
      i32_const (1l @@ at); i32_shr_s;
    ]
  | UnboxedLaxRep, UnboxedRigidRep
  | UnboxedRigidRep, UnboxedLaxRep ->
    ()
  | (BoxedRep | BlockRep), (UnboxedLaxRep | UnboxedRigidRep) ->
    (match T.norm t with
    | T.Bool | T.Byte -> emit ctxt W.[ref_as_i31; i31_get_u]
    | T.Int -> emit ctxt W.[ref_as_i31; i31_get_s]
    | T.Float ->
      let typeidx = lower_var_type ctxt at T.Float in
      emit ctxt W.[
        ref_as_data;
        rtt_canon (typeidx @@ at);
        ref_cast;
        struct_get (typeidx @@ at) (0l @@ at);
      ]
    | T.Tup [] ->
      ()
    | t ->
      let typeidx = lower_var_type ctxt at t in
      emit ctxt W.[
        ref_as_data;
        rtt_canon (typeidx @@ at);
        ref_cast;
      ]
    )
  | (UnboxedLaxRep | UnboxedRigidRep), (BoxedRep | BlockRep) ->
    (match T.norm t with
    | T.Bool | T.Byte | T.Int -> emit ctxt W.[i31_new]
    | T.Float ->
      let typeidx = lower_var_type ctxt at t in
      emit ctxt W.[rtt_canon (typeidx @@ at); struct_new (typeidx @@ at)]
    | _ -> ()
    )
  | _ -> assert false


(* Variables and Paths *)

let compile_lit ctxt l at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match l with
  | IntL i -> emit ctxt W.[i32_const (W.I32.(shr_s (shl i 1l) 1l) @@ at)]
  | FloatL z -> emit ctxt W.[f64_const (W.F64.of_float z @@ at)]
  | TextL s ->
    let addr = emit_data ctxt at s in
    emit ctxt W.[
      i32_const (addr @@ at);
      i32_const (i32 (String.length s) @@ at);
      call (Intrinsic.compile_text_new ctxt @@ at);
    ]


let rec find_var ctxt x envs : scope * loc =
  match envs with
  | [] ->
    Printf.printf "[find_var `%s` @@ %s]\n%!" x.it (Source.string_of_region x.at);
    assert false
  | (scope, env)::envs' ->
    match E.find_opt_val x !env with
    | None ->
      let (scope', _) as result = find_var ctxt x envs' in
      (match scope', scope with
      | (PreScope | GlobalScope), _
      | (LocalScope | ModuleScope), LocalScope -> ()
      | _ -> nyi x.at "outer scope variable access"
      );
      result
    | Some {it = l; _} ->
      scope, l

let compile_var ctxt x t dst =
  let scope, loc = find_var ctxt x ctxt.ext.envs in
  (match scope, loc with
  | PreScope, DirectLoc idx ->
    let _, l = List.nth Prelude.vals (Int32.to_int idx) in
    compile_lit ctxt l x.at
  | LocalScope, DirectLoc idx ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
  | ModuleScope, DirectLoc idx ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
  | GlobalScope, DirectLoc idx ->
    emit_instr ctxt x.at W.(global_get (idx @@ x.at));
  );
  compile_coerce ctxt (scope_rep scope) dst t x.at

let compile_path ctxt q t dst =
  match q.it with
  | PlainP x -> compile_var ctxt x t dst
  | QualP _ -> nyi q.at "qualified paths"

let name_of_path q =
  match q.it with
  | PlainP x -> x
  | QualP (_, x) -> x


(* Patterns *)

type pat_class = IrrelevantPat | TotalPat | PartialPat

let rec classify_pat p =
  match p.it with
  | WildP -> IrrelevantPat
  | VarP _ -> TotalPat
  | LitP _ | ConP _ -> PartialPat
  | RefP p1 | AnnotP (p1, _) -> classify_pat p1
  | TupP ps -> List.fold_left max IrrelevantPat (List.map classify_pat ps)


let rec compile_pat ctxt fail p =
  let t = Source.et p in
  let t' = lower_value_type ctxt p.at pat_rep t in
  let emit ctxt = List.iter (emit_instr ctxt p.at) in
  match p.it with
  | WildP ->
    emit ctxt W.[drop]

  | VarP x ->
    let scope, env = current_scope ctxt in
    compile_coerce ctxt pat_rep (scope_rep scope) t x.at;
    let loc =
      match scope with
      | PreScope -> assert false

      | LocalScope | ModuleScope ->
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_set (idx @@ p.at)];
        DirectLoc idx

      | GlobalScope ->
        let const = default_const ctxt x.at (scope_rep scope) t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        emit ctxt W.[global_set (idx @@ p.at)];
        DirectLoc idx
    in
    env := E.extend_val !env x loc

  | LitP l ->
    compile_coerce ctxt pat_rep UnboxedRigidRep t p.at;
    compile_lit ctxt l p.at;
    (match T.norm t with
    | T.Bool | T.Byte | T.Int -> emit ctxt W.[i32_ne]
    | T.Float -> emit ctxt W.[f64_ne]
    | T.Ref _ -> emit ctxt W.[ref_eq; i32_eqz]
    | T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_eq ctxt @@ p.at); i32_eqz]
    | _ -> assert false
    );
    emit ctxt W.[br_if (fail @@ p.at)]

  | ConP (q, ps) ->
    (match T.norm (Source.et p) with
    | T.Var (y, _) ->
      if ps = [] then begin
        compile_path ctxt q (Source.et p) BoxedRep;
        emit ctxt W.[
          ref_eq;
          i32_eqz;
          br_if (fail @@ p.at);
        ]
      end else begin
        let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
        let con = List.assoc (name_of_path q).it data in
        assert (List.length ps = List.length con.flds);
        let bt1 = W.(VarBlockType (SynVar (emit_type ctxt p.at
          (FuncDefType (FuncType ([eqreft], [datareft])))))) in
        emit_block ctxt p.at W.block bt1 (fun ctxt ->
          emit ctxt W.[
            br_on_data (0l @@ p.at);
            br ((fail +% 1l) @@ p.at);
          ]
        );
(*
        let tagt = W.(FieldType (ValueStorageType i32t, Immutable)) in
        let stypeidx = emit_type ctxt q.at W.(StructDefType (StructType [tagt])) in
        emit ctxt W.[
          rtt_canon (stypeidx @@ q.at);
          ref_cast;
          struct_get (stypeidx @@ q.at) (0l @@ q.at);
        ];
*)
        let ht = W.(defht (SynVar con.typeidx)) in
        let bt2 = W.(VarBlockType (SynVar (emit_type ctxt p.at
          (FuncDefType (FuncType ([datareft], [reft nonull ht])))))) in
        emit_block ctxt p.at W.block bt2 (fun ctxt ->
          compile_path ctxt q (Source.et p) BoxedRep;
          emit ctxt W.[
            br_on_cast (0l @@ p.at);
            br ((fail +% 1l) @@ p.at);
          ]
        );
        let tmp = emit_local ctxt p.at W.(reft null ht) in
        emit ctxt W.[local_set (tmp @@ p.at)];
        List.iteri (fun i pI ->
          if classify_pat pI > IrrelevantPat then begin
            emit ctxt W.[
              local_get (tmp @@ p.at);
              ref_as_non_null;
              struct_get (con.typeidx @@ pI.at) (i32 (i + 1) @@ pI.at);
            ];
            let tI = List.nth con.flds i in
            compile_coerce ctxt UnboxedRigidRep pat_rep tI p.at;
            compile_pat ctxt fail pI;
            compile_coerce ctxt BoxedRep pat_rep t p.at
          end
        ) ps
      end
    | _ -> assert false
    )

  | RefP p1 ->
    let typeidx = lower_var_type ctxt p.at t in
    compile_coerce ctxt pat_rep UnboxedRigidRep t p.at;
    emit ctxt W.[struct_get (typeidx @@ p.at) (0l @@ p.at)];
    compile_pat ctxt fail p1

  | TupP [] ->
    assert (pat_rep <> BlockRep);
    emit ctxt W.[drop]

  | TupP ps ->
    let typeidx = lower_var_type ctxt p.at t in
    let tmp = emit_local ctxt p.at
      (lower_value_type ctxt p.at UnboxedRigidRep t) in
    compile_coerce ctxt pat_rep UnboxedRigidRep t p.at;
    emit ctxt W.[local_set (tmp @@ p.at)];
    List.iteri (fun i pI ->
      if classify_pat pI > IrrelevantPat then begin
        emit ctxt W.[local_get (tmp @@ p.at)];
        emit ctxt W.[struct_get (typeidx @@ pI.at) (i32 i @@ pI.at)];
        compile_pat ctxt fail pI;
        compile_coerce ctxt BoxedRep pat_rep t p.at
      end
    ) ps

  | AnnotP (p1, _) ->
    compile_pat ctxt fail p1


(* Expressions *)

let rec compile_exp ctxt e dst =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE q ->
    compile_path ctxt q (Source.et e) dst

  | LitE l ->
    compile_lit ctxt l e.at;
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at

  | ConE q ->
    (match T.norm (Source.et e) with
    | T.Var (y, _) ->
      compile_path ctxt q (Source.et e) dst
    | T.Fun _ ->
      nyi e.at "partial constructor application"
    | _ ->
      assert false
    )

  | UnE (op, e1) ->
    (match op, Source.et e with
    | NegOp, T.Int -> emit ctxt W.[i32_const (0l @@ e.at)]
    | InvOp, T.Int -> emit ctxt W.[i32_const (-1l @@ e.at)]
    | _ -> ()
    );
    compile_exp ctxt e1 UnboxedLaxRep;
    (match op, T.norm (Source.et e) with
    | PosOp, T.Int -> ()
    | PosOp, T.Float -> ()
    | NegOp, T.Int -> emit ctxt W.[i32_sub]
    | NegOp, T.Float -> emit ctxt W.[f64_neg]
    | InvOp, T.Int -> emit ctxt W.[i32_xor]
    | NotOp, T.Bool -> emit ctxt W.[i32_eqz]
    | _ -> assert false
    );
    compile_coerce ctxt UnboxedLaxRep dst (Source.et e) e.at

  | BinE (e1, op, e2) ->
    let src =
      match op with
      | DivOp | ModOp | ShrOp -> UnboxedRigidRep
      | _ -> UnboxedLaxRep
    in
    compile_exp ctxt e1 src;
    compile_exp ctxt e2 src;
    (match op, T.norm (Source.et e) with
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
    | CatOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_cat ctxt @@ e.at)]
    | _ -> assert false
    );
    compile_coerce ctxt UnboxedLaxRep dst (Source.et e) e.at

  | RelE (e1, op, e2) ->
    compile_exp ctxt e1 UnboxedRigidRep;
    compile_exp ctxt e2 UnboxedRigidRep;
    (match op, T.norm (Source.et e1) with
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
    | EqOp, T.Ref _ -> emit ctxt W.[ref_eq]
    | NeOp, T.Ref _ -> emit ctxt W.[ref_eq; i32_eqz]
    | EqOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_eq ctxt @@ e.at)]
    | NeOp, T.Text ->
      emit ctxt W.[call (Intrinsic.compile_text_eq ctxt @@ e.at); i32_eqz]
    | _ -> assert false
    );
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at

  | LogE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(valbt i32t) (fun ctxt ->
      emit ctxt W.[i32_const (0l @@ e1.at)];
      compile_exp ctxt e1 UnboxedRigidRep;
      emit ctxt W.[i32_eqz; br_if (0l @@ e.at); drop];
      compile_exp ctxt e2 UnboxedRigidRep;
    );
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at

  | LogE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(valbt i32t) (fun ctxt ->
      emit ctxt W.[i32_const (1l @@ e1.at)];
      compile_exp ctxt e1 UnboxedRigidRep;
      emit ctxt W.[br_if (0l @@ e.at); drop];
      compile_exp ctxt e2 UnboxedRigidRep;
    );
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at

  | RefE e1 ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    compile_exp ctxt e1 BoxedRep;
    emit ctxt W.[
      rtt_canon (typeidx @@ e.at);
      struct_new (typeidx @@ e.at);
    ];
    compile_coerce ctxt BlockRep dst (Source.et e) e.at

  | DerefE e1 ->
    let typeidx = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1 UnboxedRigidRep;
    emit ctxt W.[struct_get (typeidx @@ e.at) (0l @@ e.at)];
    compile_coerce ctxt BoxedRep dst (Source.et e) e.at

  | AssignE (e1, e2) ->
    let typeidx = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1 UnboxedRigidRep;
    compile_exp ctxt e2 BoxedRep;
    emit ctxt W.[struct_set (typeidx @@ e.at) (0l @@ e.at)];
    compile_coerce ctxt BlockRep dst (Source.et e) e.at

  | TupE [] ->
    compile_coerce ctxt BlockRep dst (Source.et e) e.at

  | TupE es ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    List.iter (fun eI -> compile_exp ctxt eI BoxedRep) es;
    emit ctxt W.[rtt_canon (typeidx @@ e.at); struct_new (typeidx @@ e.at)];
    compile_coerce ctxt BoxedRep dst (Source.et e) e.at

  | FunE (p1, e2) ->
    nyi e.at "function expressions"
(*
    if ys <> [] && not !Flags.parametric then
      nyi d.at "generic function definitions";
    let t = snd (Source.et d) in
    let W.FuncType (ts1, ts2) = lower_func_type ctxt d.at t in
    let ts1', cast_opt =
      if pass <> FuncPass then ts1, None else
      let tcls = Option.get ctxt.ext.tcls in
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
        let _, env' = current_scope ctxt in
        env' := E.extend_val !env' x (T.FuncS, DirectLoc idx);
        let ctxt = enter_scope ctxt FuncScope in
        let _, env = current_scope ctxt in
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
              compile_var ctxt Source.(ctxt.ext.self @@ x.at) (T.Class tcls);
              emit ctxt W.[
                struct_get (cls.cls_idx @@ x.at) (cls_rtt @@ x.at);
                ref_cast;
                local_set (this @@ x.at);
              ];
              this
          in
          env :=
            E.extend_val !env Source.("this" @@ x.at) (T.LetS, DirectLoc this)
        end;
        List.iter (fun (x, _) ->
          let idx = emit_param ctxt x.at in
          env := E.extend_val !env x (T.LetS, DirectLoc idx)
        ) xts;
        compile_exp ctxt e
      )
    )
*)

  | AppE (e1, e2) ->
    let rec flat e1 es =
      match e1.it with
      | AppE (e1', e2') ->
        flat e1' (e2'::es)

      | ConE q ->
        (match T.norm (Source.et e) with
        | T.Var (y, _) ->
          let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
          let con = List.assoc (name_of_path q).it data in
          assert (List.length es = List.length con.flds);
          emit ctxt W.[i32_const (con.tag @@ q.at)];
          List.iter (fun eI -> compile_exp ctxt eI UnboxedRigidRep) es;
          compile_path ctxt q (Source.et e1) BoxedRep;
          emit ctxt W.[
            ref_as_non_null;
            struct_new (con.typeidx @@ e1.at);
          ];

        | T.Fun _ ->
          nyi e.at "partial constructor application"

        | _ ->
          assert false
        )

      | ef ->
        nyi e.at "function application"
    in flat e1 [e2]
(*
    if ts <> [] && not !Flags.parametric then nyi e.at "generic function calls";
    let t1 =
      match e1.it with
      | VarE x ->
        let scope, s, loc = find_var ctxt x ctxt.ext.envs in
        (match scope, s with
        | PreScope, _ -> assert false
        | GlobalScope, T.FuncS ->
          List.iter (fun eI ->
            compile_exp ctxt eI;
            compile_coerce_value_type ctxt eI.at (Source.et eI);
          ) es;
          emit ctxt W.[call (as_direct_loc loc @@ x.at)]
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
        let s, loc = (E.find_val x cls.env).it in
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
            struct_get (cls.disp_idx @@ e11.at) (as_direct_loc loc @@ x.at);
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
*)

  | AnnotE (e1, _t) ->
    compile_exp ctxt e1 dst

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at dst (Source.et e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      emit_block ctxt e.at W.block W.voidbt (fun ctxt ->
        compile_exp ctxt e1 UnboxedRigidRep;
        emit ctxt W.[i32_eqz; br_if (0l @@ e.at)];
        compile_exp ctxt e2 dst;
        emit ctxt W.[br (1l @@ e.at)];
      );
      compile_exp ctxt e3 dst;
    )

  | CaseE (e1, pes) ->
    let t1 = Source.et e1 in
    let tmp = emit_local ctxt e1.at (lower_value_type ctxt e1.at pat_rep t1) in
    compile_exp ctxt e1 (if pes = [] then DropRep else pat_rep);
    if pes = [] then
      emit ctxt W.[unreachable]
    else begin
      emit ctxt W.[local_set (tmp @@ e1.at)];
      let bt = lower_block_type ctxt e.at dst (Source.et e) in
      emit_block ctxt e.at W.block bt (fun ctxt ->
        let ends_with_partial =
          List.fold_left (fun _ (pI, eI) ->
            match classify_pat pI with
            | IrrelevantPat ->
              compile_exp ctxt eI dst;
              emit ctxt W.[br (0l @@ eI.at)];
              false
            | TotalPat ->
              let ctxt = enter_scope ctxt LocalScope in
              emit ctxt W.[local_get (tmp @@ pI.at)];
              compile_pat ctxt (-1l) pI;
              compile_exp ctxt eI dst;
              emit ctxt W.[br (0l @@ eI.at)];
              false
            | PartialPat ->
              let ctxt = enter_scope ctxt LocalScope in
              emit_block ctxt pI.at W.block W.voidbt (fun ctxt ->
                emit ctxt W.[local_get (tmp @@ pI.at)];
                compile_pat ctxt 0l pI;
                compile_exp ctxt eI dst;
                emit ctxt W.[br (1l @@ eI.at)];
              );
              true
          ) true pes
        in
        if ends_with_partial then emit ctxt W.[unreachable]
      )
    end

  | LetE (ds, e1) ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs FullPass ctxt ds;
    compile_exp ctxt e1 dst


(* Declarations *)

and compile_dec pass ctxt d dst =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
(*
  let scope, env = current_scope ctxt in
*)
  match d.it with
  | ExpD e ->
    compile_exp ctxt e dst

  | AssertD e ->
    compile_exp ctxt e UnboxedRigidRep;
    emit ctxt W.[i32_eqz; if_ W.voidbt [unreachable @@ d.at] []]

  | ValD (p, e) ->
    (match classify_pat p with
    | IrrelevantPat ->
      compile_exp ctxt e DropRep;
    | TotalPat ->
      compile_exp ctxt e pat_rep;
      compile_pat ctxt (-1l) p;
    | PartialPat ->
      emit_block ctxt e.at W.block W.voidbt (fun ctxt ->
        emit_block ctxt e.at W.block W.voidbt (fun ctxt ->
          compile_exp ctxt e pat_rep;
          compile_pat ctxt 0l p;
          emit ctxt W.[br (1l @@ d.at)];
        );
        emit ctxt W.[unreachable]
      )
    )
(*
    let t = snd (Source.et d) in
    let t' = lower_value_type ctxt x.at t in
    compile_exp ctxt e;
    compile_coerce_value_type ctxt e.at t;
    let loc =
      match scope with
      | PreScope -> assert false

      | BlockScope | FuncScope ->
        assert (pass = FullPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_set (idx @@ d.at)];
        DirectLoc idx

      | GlobalScope ->
        assert (pass = FullPass);
        let const = default_const ctxt x.at t in
        let idx = emit_global ctxt x.at W.Mutable t' const in
        emit ctxt W.[global_set (idx @@ d.at)];
        DirectLoc idx

      | ClassScope _ ->
        assert (pass = LetPass);
        let idx = emit_local ctxt x.at t' in
        emit ctxt W.[local_tee (idx @@ d.at)];
        DirectLoc idx
    in
    env := E.extend_val !env x (T.LetS, loc)
*)

  | TypD _ ->
    ()

  | DatD (y, _ys, xtss) ->
    let scope, env = List.hd ctxt.ext.envs in
    let tagt = W.(FieldType (ValueStorageType i32t, Immutable)) in
    let stypeidx = emit_type ctxt y.at W.(StructDefType (StructType [tagt])) in
    let rtttmp =
      if List.for_all (fun (_, ts) -> ts = []) xtss then -1l else
      let rtt = W.(RefType (Nullable, RttHeapType (SynVar stypeidx, Some 0l))) in
      let tmp = emit_local ctxt y.at rtt in
      emit ctxt W.[
        rtt_canon (stypeidx @@ y.at);
        local_set (tmp @@ y.at);
      ];
      tmp
    in
    let data =
      List.mapi (fun i (x, ts) ->
        let flds = List.map Source.et ts in
        let fts = List.map
          (lower_field_type ctxt x.at W.Immutable UnboxedRigidRep) flds in
        let ht, typeidx =
          if ts = [] then begin
            emit ctxt W.[
              i32_const (i32 i @@ x.at);
              i31_new;
            ];
            W.I31HeapType, -1l
          end else begin
            let typeidx =
              emit_type ctxt x.at W.(StructDefType (StructType (tagt::fts))) in
            emit ctxt W.[
              local_get (rtttmp @@ x.at);
              ref_as_non_null;
              rtt_sub (typeidx @@ x.at);
            ];
            W.RttHeapType (W.SynVar typeidx, Some 1l), typeidx
          end
        in
        let t = W.(RefType (Nullable, ht)) in
        let loc =
          match scope with
          | PreScope -> assert false

          | LocalScope | ModuleScope ->
            let idx = emit_local ctxt x.at t in
            emit ctxt W.[local_set (idx @@ x.at)];
            DirectLoc idx

          | GlobalScope ->
            let const = [W.ref_null ht @@ x.at] @@ x.at in
            let idx = emit_global ctxt x.at W.Mutable t const in
            emit ctxt W.[global_set (idx @@ x.at)];
            DirectLoc idx
        in
        env := E.extend_val !env x loc;
        (x.it, {tag = i32 i; typeidx; flds})
      ) (List.sort compare xtss)
    in env := E.extend_typ !env y data

  | ModD _ ->
    nyi d.at "module definitions"

  | SigD _ ->
    ()

  | RecD _ ->
    nyi d.at "recursive definitions"

  | InclD _ ->
()(*
    if d.at <> Prelude.region then nyi d.at "include declarations"
*)


and compile_decs pass ctxt ds =
  match ds with
  | [] -> ()
  | [d] -> compile_dec pass ctxt d BlockRep
  | d::ds' ->
    compile_dec pass ctxt d DropRep;
    compile_decs pass ctxt ds'

(*
and compile_scope ctxt scope ds =
  compile_decs FullPass (enter_scope ctxt scope) ds
*)


(* Programs *)

(*
let compile_imp ctxt d =
  let ImpD (xo, xs, url) = d.it in
  let _, env = current_scope ctxt in
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
      in env := E.extend_val !env x' (sort, DirectLoc idx)
  ) xs (Source.et d)
*)

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
(*
  List.iter (compile_imp ctxt) is;
*)
  let t, _ = Source.et p in
  let rep = scope_rep GlobalScope in
  let vt = lower_value_type ctxt p.at rep t in
  let const = default_const ctxt p.at rep t in
  let result_idx = emit_global ctxt p.at W.Mutable vt const in
  let start_idx =
    emit_func ctxt p.at [] [] (fun ctxt _ ->
      compile_decs FullPass ctxt ds;
      compile_coerce ctxt BlockRep rep t p.at;
      emit_instr ctxt p.at W.(global_set (result_idx @@ p.at));
    )
  in
  emit_start ctxt p.at start_idx;
  emit_global_export ctxt p.at "return" result_idx;
(*
  let _, env = current_scope ctxt in
  E.iter_vals (fun x sl ->
    let sort, loc = sl.it in
    let idx = as_direct_loc loc in
    match sort with
    | T.LetS | T.VarS | T.ClassS -> emit_global_export ctxt sl.at x idx
    | T.FuncS -> emit_func_export ctxt sl.at x idx
    | T.ProhibitedS -> assert false
  ) !env;
*)
  Emit.gen_module ctxt p.at
