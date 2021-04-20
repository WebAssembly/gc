open Source
open Syntax
open Emit
open Lower

module T = Type
module E = Env
module W = Emit.W


(* Helpers *)

let (@@) = W.Source.(@@)

let int32 = W.I32.of_int_s
let float64 = W.F64.of_float
let (+%) = Int32.add


(* Failure *)

exception NYI of Source.region * string

let _nyi at s = raise (NYI (at, s))


(* Environment *)

type data_con = {tag : int32; typeidx : int32; flds : T.typ list}
type data = (string * data_con) list
type env = (loc * func_loc option, data, loc * func_loc option, unit) E.env
type scope = PreScope | LocalScope | FuncScope | GlobalScope | ModuleScope

let make_env () =
  let env = ref Env.empty in
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region)
      (PreLoc (int32 i), None)
  ) Prelude.vals;
  env

type pass = FullPass | RecPrePass | RecPass


(* Compilation context *)

type ctxt_ext = { envs : (scope * env ref) list }
type ctxt = ctxt_ext Emit.ctxt

let make_ext_ctxt () : ctxt_ext = { envs = [(PreScope, make_env ())] }
let make_ctxt () : ctxt = Emit.make_ctxt (make_ext_ctxt ())

let enter_scope ctxt scope : ctxt =
  {ctxt with ext = {envs = (scope, ref E.empty) :: ctxt.ext.envs}}

let current_scope ctxt : scope * env ref =
  List.hd ctxt.ext.envs

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
  | PreLoc i -> "prelude" ^ Int32.to_string i
  | LocalLoc i -> "local" ^ Int32.to_string i
  | GlobalLoc i -> "global" ^ Int32.to_string i
  | ClosureLoc (i, _, _) -> "closure" ^ Int32.to_string i

let print_env env =
  E.iter_mods (fun x locs -> let l, _ = locs.it in
    Printf.printf " val(%s)=%s" x (string_of_loc l)) env;
  E.iter_vals (fun x locs -> let l, _ = locs.it in
    Printf.printf " val(%s)=%s" x (string_of_loc l)) env;
  Printf.printf "\n"

let print_envs envs =
  List.iter (fun (_, env) -> print_env !env) envs

let string_of_type ctxt idx =
  W.string_of_def_type (Emit.lookup_def_type ctxt idx)

let string_of_field_type ctxt idx i =
  let idx' = Emit.lookup_ref_field_type ctxt idx i in
  Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'
*)


(* Coercions *)

let default_exp ctxt at rep t : W.instr' list =
  if is_boxed_rep rep then
    W.[ref_null (lower_heap_type ctxt at t)]
  else
    match T.norm t with
    | T.Bool | T.Byte | T.Int ->
      W.[i32_const (0l @@ at)]
    | T.Float ->
      W.[f64_const (float64 0.0 @@ at)]
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
    emit ctxt W.[
      drop;
    ]
  | _, BlockRep when T.eq t (T.Tup []) ->
    emit ctxt W.[
      drop;
    ]
  | BlockRep, _ when T.eq t (T.Tup []) ->
    emit ctxt W.[
      ref_null (lower_heap_type ctxt at (T.Tup []))
    ]
  | BoxedRep, BlockRep
  | BlockRep, BoxedRep ->
    ()
  | UnboxedLaxRep, UnboxedRigidRep when T.eq t T.Int ->
    emit ctxt W.[
      i32_const (1l @@ at);
      i32_shl;
      i32_const (1l @@ at);
      i32_shr_s;
    ]
  | UnboxedLaxRep, UnboxedRigidRep
  | UnboxedRigidRep, UnboxedLaxRep ->
    ()
  | (BoxedRep | BlockRep), (UnboxedLaxRep | UnboxedRigidRep) ->
    (match T.norm t with
    | T.Bool | T.Byte ->
      emit ctxt W.[
        ref_as_i31;
        i31_get_u;
      ]
    | T.Int ->
      emit ctxt W.[
        ref_as_i31;
        i31_get_s;
      ]
    | T.Float ->
      let boxedfloat = lower_var_type ctxt at T.Float in
      emit ctxt W.[
        ref_as_data;
        rtt_canon (boxedfloat @@ at);
        ref_cast;
        struct_get (boxedfloat @@ at) (0l @@ at);
      ]
    | T.Tup [] ->
      ()
    | t ->
      let x = lower_var_type ctxt at t in
      emit ctxt W.[
        ref_as_data;
        rtt_canon (x @@ at);
        ref_cast;
      ]
    )
  | (UnboxedLaxRep | UnboxedRigidRep), (BoxedRep | BlockRep) ->
    (match T.norm t with
    | T.Bool | T.Byte | T.Int ->
      emit ctxt W.[
        i31_new;
      ]
    | T.Float ->
      let boxedfloat = lower_var_type ctxt at T.Float in
      emit ctxt W.[
        rtt_canon (boxedfloat @@ at);
        struct_new (boxedfloat @@ at);
      ]
    | _ -> ()
    )
  | _ -> assert false


(* Variables and Paths *)

let compile_lit ctxt l at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match l with
  | IntL i ->
    let ext_i = W.I32.(shr_s (shl i 1l) 1l) in
    emit ctxt W.[
      i32_const (ext_i @@ at);
    ]
  | FloatL z ->
    emit ctxt W.[
      f64_const (float64 z @@ at);
    ]
  | TextL s ->
    let addr = emit_data ctxt at s in
    emit ctxt W.[
      i32_const (addr @@ at);
      i32_const (int32 (String.length s) @@ at);
      call (Intrinsic.compile_text_new ctxt @@ at);
    ]


let rec find_var f ctxt x envs : loc * func_loc option =
  match envs with
  | [] ->
    Printf.printf "[find_var `%s` @@ %s]\n%!" x.it (Source.string_of_region x.at);
    assert false
  | (scope, env)::envs' ->
    match f x !env with
    | Some {it = locs; _} -> locs
    | None -> find_var f ctxt x envs'

let find_val_var = find_var E.find_opt_val
let find_mod_var = find_var E.find_opt_mod

let compile_var find_var ctxt x =
  let loc, _ = find_var ctxt x ctxt.ext.envs in
  (match loc with
  | PreLoc idx ->
    let _, l = List.nth Prelude.vals (Int32.to_int idx) in
    compile_lit ctxt l x.at
  | LocalLoc idx ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
  | GlobalLoc idx ->
    emit_instr ctxt x.at W.(global_get (idx @@ x.at));
  | ClosureLoc (idx, localidx, typeidx) ->
    emit_instr ctxt x.at W.(local_get (localidx @@ x.at));
    emit_instr ctxt x.at W.(struct_get (typeidx @@ x.at) (idx @@ x.at));
  );
  loc

let compile_val_var ctxt x t dst =
  let loc = compile_var find_val_var ctxt x in
  compile_coerce ctxt (loc_rep loc) dst t x.at

let compile_mod_var ctxt x =
  match compile_var find_mod_var ctxt x with
  | LocalLoc _ | GlobalLoc _ -> emit_instr ctxt x.at W.ref_as_non_null
  | _ -> ()

let compile_mod_proj ctxt str x =
  let _, typeidx = lower_str_type ctxt x.at str in
  let i = ref 0 in
  let found = ref false in
  E.iter_mods (fun x' _ ->
    if not !found then if x' = x.it then found := true else incr i
  ) str;
  emit_instr ctxt x.at W.(
    struct_get (typeidx @@ x.at) (int32 !i @@ x.at)
  )

let rec compile_mod_path ctxt q =
  match q.it with
  | PlainP x -> compile_mod_var ctxt x
  | QualP (q', x) ->
    compile_mod_path ctxt q';
    compile_mod_proj ctxt (snd (T.as_str (Source.et q'))) x

let compile_val_proj ctxt str x t dst =
  let _, typeidx = lower_str_type ctxt x.at str in
  let k = E.cardinal_mods str in
  let i = ref 0 in
  let found = ref false in
  E.iter_vals (fun x' _ ->
    if not !found then if x' = x.it then found := true else incr i
  ) str;
  emit_instr ctxt x.at W.(
    struct_get (typeidx @@ x.at) (int32 (k + !i) @@ x.at)
  );
  compile_coerce ctxt struct_rep dst t x.at

let compile_val_path ctxt q t dst =
  match q.it with
  | PlainP x -> compile_val_var ctxt x t dst
  | QualP (q', x) ->
    compile_mod_path ctxt q';
    compile_val_proj ctxt (snd (T.as_str (Source.et q'))) x t dst


let name_of_path q =
  match q.it with
  | PlainP x -> x
  | QualP (_, x) -> x


let rec compile_val_var_bind pass ctxt x t funcloc_opt =
  let scope, env = current_scope ctxt in
  match pass with
  | RecPrePass ->
    let loc =
      match scope with
      | PreScope -> assert false
      | LocalScope | FuncScope | ModuleScope ->
        let vt = lower_value_type ctxt x.at local_rep t in
        LocalLoc (emit_local ctxt x.at vt)
      | GlobalScope ->
        let vt = lower_value_type ctxt x.at local_rep t in
        let const = default_const ctxt x.at global_rep t in
        GlobalLoc (emit_global ctxt x.at W.Mutable vt const)
    in
    env := E.extend_val !env x (loc, funcloc_opt)

  | RecPass ->
    let loc, _ = (E.find_val x !env).it in
    compile_coerce ctxt pat_rep (loc_rep loc) t x.at;
    (match loc  with
    | PreLoc _ | ClosureLoc _ -> assert false
    | LocalLoc idx -> emit_instr ctxt x.at W.(local_set (idx @@ x.at))
    | GlobalLoc idx -> emit_instr ctxt x.at W.(global_set (idx @@ x.at))
    )

  | FullPass ->
    compile_val_var_bind RecPrePass ctxt x t funcloc_opt;
    compile_val_var_bind RecPass ctxt x t funcloc_opt


let compile_mod_var_bind ctxt x s funcloc_opt =
  let scope, env = current_scope ctxt in
  let _, typeidx = lower_sig_type ctxt x.at s in
  let loc =
    match scope with
    | PreScope -> assert false
    | LocalScope | FuncScope | ModuleScope ->
      let idx = emit_local ctxt x.at W.(ref_null_ typeidx) in
      emit_instr ctxt x.at W.(local_set (idx @@ x.at));
      LocalLoc idx
    | GlobalScope ->
      let const = W.[ref_null (type_ typeidx) @@ x.at] @@ x.at in
      let idx = emit_global ctxt x.at W.Mutable W.(ref_null_ typeidx) const in
      emit_instr ctxt x.at W.(global_set (idx @@ x.at));
      GlobalLoc idx
  in
  env := E.extend_mod !env x (loc, funcloc_opt)


(* Closures *)

let filter_loc ctxt find_var vals =
  Vars.filter (fun x ->
    match find_var ctxt Source.(x @@ no_region) ctxt.ext.envs with
    | (PreLoc _ | GlobalLoc _), _ -> false
    | (LocalLoc _ | ClosureLoc _), _ -> true
  ) vals

let filter_vars ctxt vars =
  { vals = filter_loc ctxt find_val_var vars.vals;
    mods = filter_loc ctxt find_mod_var vars.mods;
  }

let compile_load_env ctxt clos closN closNenv vars at =
  if vars <> empty then begin
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let anyclos = lower_anyclos_type ctxt at in
    let envlocal = emit_local ctxt at W.(ref_null_ closNenv) in
    emit ctxt W.[
      local_get (clos @@ at);
      rtt_canon (anyclos @@ at);
      rtt_sub (closN @@ at);
      rtt_sub (closNenv @@ at);
      ref_cast;
      local_set (envlocal @@ at);
    ];
    let _, env = current_scope ctxt in
    let clos_mod_env_len =
      Vars.fold (fun x i ->
        let idx = clos_env_idx +% i in
        let x' = Source.(@@) x at in
        let _, func_loc_opt = find_mod_var ctxt x' ctxt.ext.envs in
        env := E.extend_mod !env x'
          (ClosureLoc (idx, envlocal, closNenv), func_loc_opt);
        i +% 1l
      ) vars.mods 0l
    in
    let _ =
      Vars.fold (fun x i ->
        let idx = clos_env_idx +% i in
        let x' = Source.(@@) x at in
        let _, func_loc_opt = find_val_var ctxt x' ctxt.ext.envs in
        env := E.extend_val !env x'
          (ClosureLoc (idx, envlocal, closNenv), func_loc_opt);
        i +% 1l
      ) vars.vals clos_mod_env_len
    in ()
  end

let compile_alloc_clos ctxt fn arity vars closN closNenv at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  let anyclos = lower_anyclos_type ctxt at in
  emit_func_ref ctxt at fn;
  emit ctxt W.[
    i32_const (int32 arity @@ at);
    ref_func (fn @@ at);
  ];
  Vars.iter (fun x ->
    compile_mod_var ctxt (Source.(@@) x at)
  ) vars.mods;
  Vars.iter (fun x ->
    compile_val_var ctxt (Source.(@@) x at)
      (T.Var ("", [])) (loc_rep (ClosureLoc (0l, 0l, 0l))) (* TODO *)
  ) vars.vals;
  emit ctxt W.[
    rtt_canon (anyclos @@ at);
    rtt_sub (closN @@ at);
  ];
  if vars <> empty then begin
    emit ctxt W.[
      rtt_sub (closNenv @@ at);
    ]
  end;
  emit ctxt W.[
    struct_new (closNenv @@ at);
  ]


(* Patterns *)

type pat_class = IrrelevantPat | TotalPat | PartialPat

let rec classify_pat p =
  match p.it with
  | WildP -> IrrelevantPat
  | VarP _ -> TotalPat
  | LitP _ | ConP _ -> PartialPat
  | RefP p1 | AnnotP (p1, _) -> classify_pat p1
  | TupP ps -> List.fold_left max IrrelevantPat (List.map classify_pat ps)

let rec compile_pat pass ctxt fail p =
  let t = Source.et p in
  let emit ctxt = List.iter (emit_instr ctxt p.at) in
  match p.it with
  | WildP | LitP _ when pass = RecPrePass ->
    ()

  | WildP ->
    emit ctxt W.[
      drop;
    ]

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
    emit ctxt W.[
      br_if (fail @@ p.at);
    ]

  | VarP x ->
    compile_val_var_bind pass ctxt x t None

  | TupP ps | ConP (_, ps) when pass = RecPrePass ->
    List.iter (compile_pat pass ctxt fail) ps

  | TupP [] ->
    assert (pat_rep <> BlockRep);
    emit ctxt W.[
      drop;
    ]

  | TupP ps ->
    let tmp =
      emit_local ctxt p.at (lower_value_type ctxt p.at UnboxedRigidRep t) in
    compile_coerce ctxt pat_rep UnboxedRigidRep t p.at;
    emit ctxt W.[
      local_set (tmp @@ p.at);
    ];
    List.iteri (fun i pI ->
      if classify_pat pI > IrrelevantPat then begin
        emit ctxt W.[
          local_get (tmp @@ p.at);
          struct_get (lower_var_type ctxt p.at t @@ pI.at) (int32 i @@ pI.at);
        ];
        compile_pat pass ctxt fail pI;
        compile_coerce ctxt BoxedRep pat_rep t p.at
      end
    ) ps

  | ConP (q, []) ->
    compile_val_path ctxt q (Source.et p) BoxedRep;
    emit ctxt W.[
      ref_eq;
      i32_eqz;
      br_if (fail @@ p.at);
    ]

  | ConP (q, ps) ->
    (match T.norm (Source.et p) with
    | T.Var (y, _) ->
      let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
      let con = List.assoc (name_of_path q).it data in
      assert (List.length ps = List.length con.flds);
      let bt1 = emit_type ctxt p.at W.(type_func [boxedref] [dataref]) in
      emit_block ctxt p.at W.block W.(typeuse bt1) (fun ctxt ->
        emit ctxt W.[
          br_on_data (0l @@ p.at);
          br (fail +% 1l @@ p.at);
        ]
      );
      let bt2 = emit_type ctxt p.at W.(type_func [dataref] [ref_ con.typeidx]) in
      emit_block ctxt p.at W.block W.(typeuse bt2) (fun ctxt ->
        compile_val_path ctxt q (Source.et p) BoxedRep;
        emit ctxt W.[
          br_on_cast (0l @@ p.at);
          br (fail +% 1l @@ p.at);
        ]
      );
      let tmp = emit_local ctxt p.at W.(ref_null_ con.typeidx) in
      emit ctxt W.[local_set (tmp @@ p.at)];
      List.iteri (fun i pI ->
        if classify_pat pI > IrrelevantPat then begin
          emit ctxt W.[
            local_get (tmp @@ p.at);
            ref_as_non_null;
            struct_get (con.typeidx @@ pI.at) (int32 (i + 1) @@ pI.at);
          ];
          let tI = List.nth con.flds i in
          compile_coerce ctxt UnboxedRigidRep pat_rep tI p.at;
          compile_pat pass ctxt fail pI;
          compile_coerce ctxt BoxedRep pat_rep t p.at
        end
      ) ps
    | _ -> assert false
    )

  | RefP p1 when pass = RecPrePass ->
    compile_pat pass ctxt fail p1

  | RefP p1 ->
    let typeidx = lower_var_type ctxt p.at t in
    compile_coerce ctxt pat_rep UnboxedRigidRep t p.at;
    emit ctxt W.[
      struct_get (typeidx @@ p.at) (0l @@ p.at);
    ];
    compile_pat pass ctxt fail p1

  | AnnotP (p1, _) ->
    compile_pat pass ctxt fail p1


(* Expressions *)

let rec compile_exp ctxt dst e = ignore (compile_exp_func_opt ctxt dst e)

and compile_exp_func_opt ctxt dst e : func_loc option =
  let emit ctxt = List.iter (emit_instr ctxt e.at) in
  match e.it with
  | VarE {it = PlainP x; _} ->
    compile_val_var ctxt x (Source.et e) dst;
    let _, func_loc_opt = find_val_var ctxt x ctxt.ext.envs in
    func_loc_opt

  | VarE q ->
    compile_val_path ctxt q (Source.et e) dst;
    None

  | LitE l ->
    compile_lit ctxt l e.at;
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at;
    None

  | ConE q ->
    (match T.norm (Source.et e) with
    | T.Var (y, _) ->
      compile_val_path ctxt q (Source.et e) dst;
      None

    | T.Fun _ as t ->
      (* TODO: refactor to avoid duplicating this code *)
      let rec eta t =
        match T.norm t with
        | T.Var (y, _) ->
          let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
          let con = List.assoc (name_of_path q).it data in
          let arity = List.length con.flds in
          let _code, clos = lower_func_type ctxt e.at arity in
          let argts, argv_opt = lower_param_types ctxt e.at arity in
          let fn = emit_func ctxt e.at W.(ref_ clos :: argts) [boxedref]
            (fun ctxt _ ->
              let ctxt = enter_scope ctxt FuncScope in
              let _clos = emit_param ctxt e.at in
              let args = List.map (fun _ -> emit_param ctxt e.at) argts in
              let arg0 = List.hd args in
              emit ctxt W.[
                i32_const (con.tag @@ q.at);
              ];
              List.iteri (fun i _ ->
                let tI = T.norm (List.nth con.flds i) in
                Intrinsic.compile_load_arg ctxt e.at i arg0 argv_opt;
                compile_coerce ctxt BoxedRep UnboxedRigidRep tI e.at;
              ) con.flds;
              compile_val_path ctxt q (Source.et e) BoxedRep;
              emit ctxt W.[
                ref_as_non_null;
                struct_new (con.typeidx @@ e.at);
              ]
            )
          in
          emit_func_ref ctxt e.at fn;
          emit ctxt W.[
            i32_const (int32 arity @@ e.at);
            ref_func (fn @@ e.at);
            rtt_canon (lower_anyclos_type ctxt e.at @@ e.at);
            rtt_sub (clos @@ e.at);
            struct_new (clos @@ e.at);
          ];
          Some {funcidx = fn; arity}

        | T.Fun (_, t') -> eta t'

        | _ -> assert false
      in eta t

    | _ ->
      assert false
    )

  | UnE (op, e1) ->
    (match op, Source.et e with
    | NegOp, T.Int -> emit ctxt W.[i32_const (0l @@ e.at)]
    | InvOp, T.Int -> emit ctxt W.[i32_const (-1l @@ e.at)]
    | _ -> ()
    );
    compile_exp ctxt UnboxedLaxRep e1;
    (match op, T.norm (Source.et e) with
    | PosOp, T.Int -> ()
    | PosOp, T.Float -> ()
    | NegOp, T.Int -> emit ctxt W.[i32_sub]
    | NegOp, T.Float -> emit ctxt W.[f64_neg]
    | InvOp, T.Int -> emit ctxt W.[i32_xor]
    | NotOp, T.Bool -> emit ctxt W.[i32_eqz]
    | _ -> assert false
    );
    compile_coerce ctxt UnboxedLaxRep dst (Source.et e) e.at;
    None

  | BinE (e1, op, e2) ->
    let src =
      match op with
      | DivOp | ModOp | ShrOp -> UnboxedRigidRep
      | _ -> UnboxedLaxRep
    in
    compile_exp ctxt src e1;
    compile_exp ctxt src e2;
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
    compile_coerce ctxt UnboxedLaxRep dst (Source.et e) e.at;
    None

  | RelE (e1, op, e2) ->
    compile_exp ctxt UnboxedRigidRep e1;
    compile_exp ctxt UnboxedRigidRep e2;
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
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at;
    None

  | LogE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
      emit ctxt W.[
        i32_const (0l @@ e1.at);
      ];
      compile_exp ctxt UnboxedRigidRep e1;
      emit ctxt W.[
        i32_eqz;
        br_if (0l @@ e.at);
        drop;
      ];
      compile_exp ctxt UnboxedRigidRep e2;
    );
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at;
    None

  | LogE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
      emit ctxt W.[
        i32_const (1l @@ e1.at);
      ];
      compile_exp ctxt UnboxedRigidRep e1;
      emit ctxt W.[
        br_if (0l @@ e.at);
        drop;
      ];
      compile_exp ctxt UnboxedRigidRep e2;
    );
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at;
    None

  | RefE e1 ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    compile_exp ctxt BoxedRep e1;
    emit ctxt W.[
      rtt_canon (typeidx @@ e.at);
      struct_new (typeidx @@ e.at);
    ];
    compile_coerce ctxt BlockRep dst (Source.et e) e.at;
    None

  | DerefE e1 ->
    let typ = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt UnboxedRigidRep e1;
    emit ctxt W.[
      struct_get (typ @@ e.at) (0l @@ e.at);
    ];
    compile_coerce ctxt BoxedRep dst (Source.et e) e.at;
    None

  | AssignE (e1, e2) ->
    let typ = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt UnboxedRigidRep e1;
    compile_exp ctxt BoxedRep e2;
    emit ctxt W.[
      struct_set (typ @@ e.at) (0l @@ e.at);
    ];
    compile_coerce ctxt BlockRep dst (Source.et e) e.at;
    None

  | TupE [] ->
    compile_coerce ctxt BlockRep dst (Source.et e) e.at;
    None

  | TupE es ->
    let typ = lower_var_type ctxt e.at (Source.et e) in
    List.iter (compile_exp ctxt BoxedRep) es;
    emit ctxt W.[
      rtt_canon (typ @@ e.at);
      struct_new (typ @@ e.at);
    ];
    compile_coerce ctxt BoxedRep dst (Source.et e) e.at;
    None

  | FunE (p1, e2) ->
    let rec flat ps e2 =
      match e2.it with
      | FunE (p, e22) -> flat (p::ps) e22
      | _ ->
        let vars = filter_vars ctxt (free_exp e) in
        let envts = List.init (cardinal vars) (fun _ -> boxedref) in
        let ps = List.rev ps in
        let arity = List.length ps in
        let _code, closN, closNenv = lower_clos_type ctxt e.at arity envts in
        let argts, argv_opt = lower_param_types ctxt e.at arity in
        let fn = emit_func ctxt e.at W.(ref_ closN :: argts) [boxedref]
          (fun ctxt _ ->
            let ctxt = enter_scope ctxt FuncScope in
            let clos = emit_param ctxt e2.at in
            let args = List.map (fun _ -> emit_param ctxt e2.at) argts in
            let arg0 = List.hd args in
            compile_load_env ctxt clos closN closNenv vars e2.at;

            let partial = List.exists (fun p -> classify_pat p = PartialPat) ps in
            if not partial then
              List.iteri (fun i pI ->
                match classify_pat pI with
                | IrrelevantPat -> ()
                | TotalPat ->
                  Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                  compile_pat FullPass ctxt (-1l) pI;
                | PartialPat -> assert false
              ) ps
            else
              emit_block ctxt e.at W.block W.void (fun ctxt ->
                emit_block ctxt e.at W.block W.void (fun ctxt ->
                  List.iteri (fun i pI ->
                    match classify_pat pI with
                    | IrrelevantPat -> ()
                    | TotalPat ->
                      Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                      compile_pat FullPass ctxt (-1l) pI;
                    | PartialPat ->
                      Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                      compile_pat FullPass ctxt 0l pI;
                  ) ps;
                  emit ctxt W.[br (1l @@ e.at)];
                );
                emit ctxt W.[unreachable]
              );
            compile_exp ctxt BoxedRep e2
          )
        in
        compile_alloc_clos ctxt fn (List.length ps) vars closN closNenv e.at;
        Some {funcidx = fn; arity = List.length ps}
    in flat [p1] e2

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
          emit ctxt W.[
            i32_const (con.tag @@ q.at);
          ];
          List.iteri (fun i eI ->
            let rep =
              match T.norm (List.nth con.flds i) with
              | T.Var _ -> BoxedRep
              | _ -> UnboxedRigidRep
            in compile_exp ctxt rep eI
          ) es;
          compile_val_path ctxt q (Source.et e1) BoxedRep;
          emit ctxt W.[
            ref_as_non_null;
            struct_new (con.typeidx @@ e1.at);
          ];

        | T.Fun _ ->
          compile_exp ctxt UnboxedRigidRep e1;
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt BoxedRep (List.nth es i)
          );
          emit ctxt W.[
            call (Intrinsic.compile_apply ctxt (List.length es) @@ e.at);
          ]

        | _ ->
          assert false
        )

      | _ ->
        (match compile_exp_func_opt ctxt UnboxedRigidRep e1 with
        | Some {funcidx; arity} when arity = List.length es ->
          let anyclos = lower_anyclos_type ctxt e1.at in
          let _, closN = lower_func_type ctxt e1.at arity in
          emit ctxt W.[
            rtt_canon (anyclos @@ e1.at);
            rtt_sub (closN @@ e1.at);
            ref_cast;
          ];
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt BoxedRep (List.nth es i)
          );
          emit ctxt W.[
            call (funcidx @@ e.at);
          ]
        | _ ->
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt BoxedRep (List.nth es i)
          );
          emit ctxt W.[
            call (Intrinsic.compile_apply ctxt (List.length es) @@ e.at);
          ]
        );
        compile_coerce ctxt BoxedRep dst (Source.et e) e.at
    in flat e1 [e2];
    None

  | AnnotE (e1, _t) ->
    compile_exp_func_opt ctxt dst e1

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at dst (Source.et e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      emit_block ctxt e.at W.block W.void (fun ctxt ->
        compile_exp ctxt UnboxedRigidRep e1;
        emit ctxt W.[
          i32_eqz;
          br_if (0l @@ e.at);
        ];
        compile_exp ctxt dst e2;
        emit ctxt W.[
          br (1l @@ e.at);
        ];
      );
      compile_exp ctxt dst e3;
    );
    None

  | CaseE (e1, []) ->
    compile_exp ctxt pat_rep e1;
    emit ctxt W.[
      unreachable;
    ];
    None

  | CaseE (e1, pes) ->
    let t1 = Source.et e1 in
    let tmp = emit_local ctxt e1.at (lower_value_type ctxt e1.at pat_rep t1) in
    compile_exp ctxt pat_rep e1;
    emit ctxt W.[
      local_set (tmp @@ e1.at);
    ];
    let bt = lower_block_type ctxt e.at dst (Source.et e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      let ends_with_partial =
        List.fold_left (fun _ (pI, eI) ->
          match classify_pat pI with
          | IrrelevantPat ->
            compile_exp ctxt dst eI;
            emit ctxt W.[br (0l @@ eI.at)];
            false
          | TotalPat ->
            let ctxt = enter_scope ctxt LocalScope in
            emit ctxt W.[local_get (tmp @@ pI.at)];
            compile_pat FullPass ctxt (-1l) pI;
            compile_exp ctxt dst eI;
            emit ctxt W.[br (0l @@ eI.at)];
            false
          | PartialPat ->
            let ctxt = enter_scope ctxt LocalScope in
            emit_block ctxt pI.at W.block W.void (fun ctxt ->
              emit ctxt W.[local_get (tmp @@ pI.at)];
              compile_pat FullPass ctxt 0l pI;
              compile_exp ctxt dst eI;
              emit ctxt W.[br (1l @@ eI.at)];
            );
            true
        ) true pes
      in
      if ends_with_partial then emit ctxt W.[unreachable]
    );
    None

  | LetE (ds, e1) ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs FullPass ctxt ds;
    compile_exp_func_opt ctxt dst e1


(* Modules *)

and compile_mod ctxt m = ignore (compile_mod_func_opt ctxt m)

and compile_mod_func_opt ctxt m : func_loc option =
  let emit ctxt = List.iter (emit_instr ctxt m.at) in
  match m.it with
  | VarM {it = PlainP x; _} ->
    compile_mod_var ctxt x;
    let _, func_loc_opt = find_mod_var ctxt x ctxt.ext.envs in
    func_loc_opt

  | VarM q ->
    compile_mod_path ctxt q;
    None

  | StrM ds ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs FullPass ctxt ds;
    let vars = Syntax.list bound_dec ds in
    let _, str = lower_sig_type ctxt m.at (Source.et m) in
    Vars.iter (fun x ->
      compile_mod_var ctxt Source.(x @@ m.at)
    ) vars.mods;
    Vars.iter (fun x ->
      compile_val_var ctxt Source.(x @@ m.at)
        (T.Var ("", []) (*TODO*)) struct_rep
    ) vars.vals;
    emit ctxt W.[
      rtt_canon (str @@ m.at);
      struct_new (str @@ m.at);
    ];
    None

  | FunM (x, _s, m2) ->
    let vars = filter_vars ctxt (free_mod m) in
    let envts = List.init (cardinal vars) (fun _ -> boxedref) in
    let _, s1, s2 = T.as_fct (Source.et m) in
    let _code, closN, closNenv = lower_fct_clos_type ctxt m.at s1 s2 envts in
    let vt1, _ = lower_sig_type ctxt x.at s1 in
    let vt2, _ = lower_sig_type ctxt m2.at s2 in
    let fn = emit_func ctxt m.at W.(ref_ closN :: [vt1]) [vt2]
      (fun ctxt _ ->
        let ctxt = enter_scope ctxt FuncScope in
        let _, env = current_scope ctxt in
        let clos = emit_param ctxt m2.at in
        let arg = emit_param ctxt m2.at in
        compile_load_env ctxt clos closN closNenv vars m2.at;
        env := E.extend_mod !env x (LocalLoc arg, None);
        compile_mod ctxt m2
      )
    in
    compile_alloc_clos ctxt fn 1 vars closN closNenv m.at;
    Some {funcidx = fn; arity = 1}

  | AppM (m1, m2) ->
    let anyclos = lower_anyclos_type ctxt m1.at in
    let _, clos1 = lower_sig_type ctxt m1.at (Source.et m1) in
    let _, s11, _ = T.as_fct (Source.et m1) in
    let func_loc_opt = compile_mod_func_opt ctxt m1 in
    emit ctxt W.[
      rtt_canon (anyclos @@ m1.at);
      rtt_sub (clos1 @@ m1.at);
      ref_cast;
    ];
    (match func_loc_opt with
    | Some {funcidx; _} ->
      compile_mod ctxt m2;
      compile_coerce_mod ctxt (Source.et m2) s11 m2.at;
      emit ctxt W.[
        call (funcidx @@ m.at);
      ]
    | None ->
      let tmp = emit_local ctxt m.at W.(ref_null_ clos1) in
      emit ctxt W.[
        local_tee (tmp @@ m1.at);
        ref_as_non_null;
      ];
      compile_mod ctxt m2;
      compile_coerce_mod ctxt (Source.et m2) s11 m2.at;
      emit ctxt W.[
        local_get (tmp @@ m1.at);
        struct_get (clos1 @@ m1.at) (clos_code_idx @@ m1.at);
        call_ref;
      ]
    );
    None

  | AnnotM (m1, _s) ->
    compile_mod ctxt m1;
    compile_coerce_mod ctxt (Source.et m1) (Source.et m) m.at;
    None

  | LetM (ds, m1) ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs FullPass ctxt ds;
    compile_mod_func_opt ctxt m1


and compile_coerce_mod ctxt s1 s2 at =
  if need_coerce_mod s1 s2 then begin
    let emit ctxt = List.iter (emit_instr ctxt at) in
    match s1, s2 with
    | T.Str (_, str1), T.Str (_, str2) ->
      let t1, tidx = lower_str_type ctxt at str1 in
      let _, typeidx2 = lower_str_type ctxt at str2 in
      let tmp = emit_local ctxt at W.(ref_null_ tidx) in
      emit ctxt W.[
        local_set (tmp @@ at);
      ];
      E.iter_mods (fun x s2 ->
        let s1 = E.find_mod (Source.(@@) x at) str1 in
        emit_instr ctxt at W.(local_get (tmp @@ at));
        compile_mod_proj ctxt str1 (Source.(@@) x at);
        compile_coerce_mod ctxt s1.it s2.it at;
      ) str2;
      E.iter_vals (fun x _ ->
        emit_instr ctxt at W.(local_get (tmp @@ at));
        compile_val_proj ctxt str1 (Source.(@@) x at)
          (*TODO*) (T.Var ("", [])) struct_rep;
      ) str2;
      emit ctxt W.[
        rtt_canon (typeidx2 @@ at);
        struct_new (typeidx2 @@ at);
      ];

    | T.Fct (_, s11, s12), T.Fct (_, s21, s22) ->
      let ft, fidx = lower_sig_type ctxt at s1 in
      let anyclos = lower_anyclos_type ctxt at in
      let _code, clos1, closenv = lower_fct_clos_type ctxt at s12 s22 [ft] in
      let vt21, _ = lower_sig_type ctxt at s21 in
      let vt22, _ = lower_sig_type ctxt at s22 in
      let fn = emit_func ctxt at W.(ref_ clos1 :: [vt21]) [vt22]
        (fun ctxt _ ->
          let clos = emit_param ctxt at in
          let arg = emit_param ctxt at in
          let tmp = emit_local ctxt at W.(ref_null_ fidx) in
          emit ctxt W.[
            local_get (clos @@ at);
            rtt_canon (anyclos @@ at);
            rtt_sub (clos1 @@ at);
            rtt_sub (closenv @@ at);
            ref_cast;
            struct_get (closenv @@ at) (clos_env_idx @@ at);
            local_tee (tmp @@ at);
            ref_as_non_null;
            local_get (arg @@ at);
          ];
          compile_coerce_mod ctxt s21 s11 at;
          emit ctxt W.[
            local_get (tmp @@ at);
            struct_get (fidx @@ at) (clos_code_idx @@ at);
            call_ref;
          ];
          compile_coerce_mod ctxt s12 s22 at;
        )
      in
      let tmp = emit_local ctxt at W.(ref_null_ fidx) in
      emit_func_ref ctxt at fn;
      emit ctxt W.[
        local_set (tmp @@ at);
        i32_const (1l @@ at);
        ref_func (fn @@ at);
        local_get (tmp @@ at);
        ref_as_non_null;
        rtt_canon (anyclos @@ at);
        rtt_sub (clos1 @@ at);
        rtt_sub (closenv @@ at);
        struct_new (closenv @@ at);
      ]

    | _ ->
      assert false
  end

and need_coerce_mod s1 s2 =
  match s1, s2 with
  | T.Str (_, str1), T.Str (_, str2) ->
    E.cardinal_vals str1 > E.cardinal_vals str2 ||
    E.cardinal_mods str1 > E.cardinal_mods str2 ||
    List.exists2 (fun (x1, s1) (x2, s2) -> need_coerce_mod s1.it s2.it)
      (E.mods str1) (E.mods str2)
  | T.Fct (_, s11, s12), T.Fct (_, s21, s22) ->
    need_coerce_mod s21 s11 || need_coerce_mod s12 s22
  | _ ->
    assert false


(* Declarations *)

and compile_dec pass ctxt d dst =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
  let scope, env = current_scope ctxt in
  match d.it with
  | ExpD _ | AssertD _ when pass = RecPrePass ->
    ()

  | ExpD e ->
    compile_exp ctxt dst e

  | AssertD e ->
    compile_exp ctxt UnboxedRigidRep e;
    emit ctxt W.[
      i32_eqz;
      if_ W.void [unreachable @@ d.at] [];
    ]

  | ValD (p, _) when pass = RecPrePass ->
    compile_pat pass ctxt (-1l) p
    (* TODO: allocate funcidx to allow static calls in recursion *)

  | ValD ({it = VarP x; _} as p, e) ->
    let idx_opt = compile_exp_func_opt ctxt pat_rep e in
    compile_pat pass ctxt (-1l) p;
    let {it = (loc, _); _} = E.find_val x !env in
    env := E.extend_val !env x (loc, idx_opt)

  | ValD (p, e) ->
    (match classify_pat p with
    | IrrelevantPat ->
      compile_exp ctxt DropRep e;
    | TotalPat ->
      compile_exp ctxt pat_rep e;
      compile_pat pass ctxt (-1l) p;
    | PartialPat ->
      emit_block ctxt e.at W.block W.void (fun ctxt ->
        emit_block ctxt e.at W.block W.void (fun ctxt ->
          compile_exp ctxt pat_rep e;
          compile_pat pass ctxt 0l p;
          emit ctxt W.[br (1l @@ d.at)];
        );
        emit ctxt W.[unreachable]
      )
    )

  | TypD _ ->
    ()

  | DatD _ when pass = RecPrePass ->
    ()

  | DatD (y, _ys, xtss) ->
    let tagged = emit_type ctxt y.at W.(type_struct [field i32]) in
    let rtttmp =
      if List.for_all (fun (_, ts) -> ts = []) xtss then -1l else
      let tmp = emit_local ctxt y.at W.(ref_null_heap (rtt_n tagged 0l)) in
      emit ctxt W.[
        rtt_canon (tagged @@ y.at);
        local_set (tmp @@ y.at);
      ];
      tmp
    in
    let data =
      List.mapi (fun i (x, ts) ->
        let flds = List.map Source.et ts in
        let ht, typeidx =
          if ts = [] then begin
            emit ctxt W.[
              i32_const (int32 i @@ x.at);
              i31_new;
            ];
            W.i31, -1l
          end else begin
            let ts = List.map (lower_value_type ctxt x.at UnboxedRigidRep) flds in
            let fts = List.map W.field ts in
            let con = emit_type ctxt x.at W.(type_struct (field i32 :: fts)) in
            emit ctxt W.[
              local_get (rtttmp @@ x.at);
              ref_as_non_null;
              rtt_sub (con @@ x.at);
            ];
            W.rtt_n con 1l, con
          end
        in
        let t = W.ref_null_heap ht in
        let loc =
          match scope with
          | PreScope -> assert false

          | LocalScope | FuncScope | ModuleScope ->
            let idx = emit_local ctxt x.at t in
            emit ctxt W.[local_set (idx @@ x.at)];
            LocalLoc idx

          | GlobalScope ->
            let const = [W.ref_null ht @@ x.at] @@ x.at in
            let idx = emit_global ctxt x.at W.Mutable t const in
            emit ctxt W.[global_set (idx @@ x.at)];
            GlobalLoc idx
        in
        env := E.extend_val !env x (loc, None);
        (x.it, {tag = int32 i; typeidx; flds})
      ) (List.sort compare xtss)
    in env := E.extend_typ !env y data

  | ModD (x, m) ->
    let funcloc_opt = compile_mod_func_opt ctxt m in
    compile_mod_var_bind ctxt x (Source.et m) funcloc_opt

  | SigD _ ->
    ()

  | RecD ds when pass <> FullPass ->
    compile_decs pass ctxt ds

  | RecD ds ->
    compile_decs RecPrePass ctxt ds;
    compile_decs RecPass ctxt ds

  | InclD m ->
    let _, str = T.as_str (Source.et m) in
    let t, tidx = lower_str_type ctxt m.at str in
    let tmp = emit_local ctxt m.at W.(ref_null_ tidx) in
    compile_mod ctxt m;
    emit ctxt W.[
      local_set (tmp @@ m.at);
    ];
    E.iter_mods (fun x' s ->
      let x = Source.(x' @@ s.at) in
      emit_instr ctxt m.at W.(local_get (tmp @@ m.at));
      compile_mod_proj ctxt str x;
      compile_mod_var_bind ctxt x s.it None;
    ) str;
    E.iter_vals (fun x' pt ->
      let x = Source.(x' @@ pt.at) in
      let T.Forall (_, t) = pt.it in
      emit_instr ctxt m.at W.(local_get (tmp @@ m.at));
      compile_val_proj ctxt str x t struct_rep;
      compile_val_var_bind FullPass ctxt x t None
    ) str

and compile_decs pass ctxt ds =
  match ds with
  | [] -> ()
  | [d] -> compile_dec pass ctxt d BlockRep
  | d::ds' ->
    compile_dec pass ctxt d DropRep;
    compile_decs pass ctxt ds'


(* Programs *)

let compile_imp ctxt d =
  let ImpD (x, url) = d.it in
  let vt, _ = lower_str_type ctxt x.at (Source.et d) in
  let idx = emit_global_import ctxt x.at url x.it W.Immutable vt in
  let _, env = current_scope ctxt in
  env := E.extend_mod !env x (GlobalLoc idx, None)

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
  List.iter (compile_imp ctxt) is;
  let t, _ = Source.et p in
  let rep = loc_rep (GlobalLoc 0l) in
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
(*TODO
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
