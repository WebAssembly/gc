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


(* Debug printing *)

(*
let string_of_null = function
  | Null -> "0"
  | Nonull -> ""

let string_of_rep = function
  | DropRep -> "drop"
  | BlockRep n -> "block" ^ string_of_null n
  | BoxedRep n -> "boxed" ^ string_of_null n
  | BoxedAbsRep n -> "abs" ^ string_of_null n
  | UnboxedRep n -> "unboxed" ^ string_of_null n
  | UnboxedLaxRep n -> "lax" ^ string_of_null n

let string_of_loc = function
  | PreLoc i -> "prelude" ^ Int32.to_string i
  | LocalLoc i -> "local" ^ Int32.to_string i
  | GlobalLoc i -> "global" ^ Int32.to_string i
  | ClosureLoc (_, i, _, _) -> "closure" ^ Int32.to_string i

let print_env env =
  E.iter_mods (fun x locs -> let l, flo = locs.it in
    Printf.printf " %s(%s)=%s" (if flo = None then "val" else "fun") x
      (string_of_loc l)) env;
  E.iter_vals (fun x locs -> let l, flo = locs.it in
    Printf.printf " %s(%s)=%s" (if flo = None then "val" else "fun") x
      (string_of_loc l)) env;
  Printf.printf "\n"

let print_envs envs =
  List.iter (fun (_, env) -> print_env !env) envs

let string_of_type ctxt idx =
  W.string_of_ctx_type (Emit.lookup_ctx_type ctxt idx)

let string_of_field_type ctxt idx i =
  let idx' = Emit.lookup_ref_field_type ctxt idx i in
  Int32.to_string idx' ^ " = " ^ string_of_type ctxt idx'

let mark ctxt i =
  emit_instr ctxt no_region W.(i32_const (i @@ no_region));
  emit_instr ctxt no_region W.drop
*)


(* Intrinsics *)

let intrinsic compile import =
  (if !Flags.headless then compile else import)

let intrinsic_text_new c = intrinsic Intrinsic.compile_text_new Runtime.import_text_new c
let intrinsic_text_cat c = intrinsic Intrinsic.compile_text_cat Runtime.import_text_cat c
let intrinsic_text_eq c = intrinsic Intrinsic.compile_text_eq Runtime.import_text_eq c
let intrinsic_func_apply n c = intrinsic Intrinsic.compile_func_apply Runtime.import_func_apply n c


(* Allocate data *)

let data_list data_e ctxt es data =
  List.fold_left (fun data eI -> data_e ctxt eI data) data es

let data_lit ctxt l at data =
  match l with
  | BoolL _ | IntL _ | FloatL _ -> data
  | TextL s ->
    ignore (Runtime.import_mem_alloc ctxt);
    ignore (Runtime.import_text_new ctxt);
    if Env.Map.find_opt s !(ctxt.ext.texts) <> None then data else
    let addr = int32 (String.length data) in
    ctxt.ext.texts := Env.Map.add s addr !(ctxt.ext.texts);
    data ^ s

let rec data_pat ctxt p data =
  match p.it with
  | WildP | VarP _ -> data
  | LitP l ->
    (match T.norm (Source.et p) with
    | T.Text -> ignore (Runtime.import_text_eq ctxt)
    | _ -> ()
    );
    data_lit ctxt l p.at data
  | ConP (_, ps) | TupP ps -> data_list data_pat ctxt ps data
  | RefP p | AnnotP (p, _) -> data_pat ctxt p data

let rec data_exp ctxt e data =
  match e.it with
  | VarE _ | ConE _ -> data
  | LitE l -> data_lit ctxt l e.at data
  | BinE (e1, CatOp, e2) ->
    ignore (Runtime.import_text_cat ctxt);
    data_list data_exp ctxt [e1; e2] data
  | RelE (e1, (EqOp | NeOp), e2) when T.eq (Source.et e1) T.Text ->
    ignore (Runtime.import_text_eq ctxt);
    data_list data_exp ctxt [e1; e2] data
  | UnE (_, e1) | RefE e1 | DerefE e1 | AnnotE (e1, _) -> data_exp ctxt e1 data
  | BinE (e1, _, e2) | LogE (e1, _, e2) | RelE (e1, _, e2) | AssignE (e1, e2) ->
    data_list data_exp ctxt [e1; e2] data
  | TupE es -> data_list data_exp ctxt es data
  | FunE (p1, e2) -> data_match ctxt (p1, e2) data
  | AppE (e1, e2) ->
    let rec flat e1 es =
      match e1.it with
      | AppE (e1', e2') -> flat e1' (e2'::es)
      | _ -> ignore (Runtime.import_func_apply (List.length es) ctxt)
    in flat e1 [e2];
    data_list data_exp ctxt [e1; e2] data
  | IfE (e1, e2, e3) -> data_list data_exp ctxt [e1; e2; e3] data
  | CaseE (e1, ms) -> data_list data_match ctxt ms (data_exp ctxt e1 data)
  | PackE (m, _) -> data_mod ctxt m data
  | LetE (ds, e2) -> data_exp ctxt e2 (data_list data_dec ctxt ds data)

and data_match ctxt (p, e) data =
  data_exp ctxt e (data_pat ctxt p data)

and data_dec ctxt d data =
  match d.it with
  | ExpD e | AssertD e -> data_exp ctxt e data
  | ValD (p, e) -> data_match ctxt (p, e) data
  | ModD (_, m) | InclD m -> data_mod ctxt m data
  | RecD ds -> data_list data_dec ctxt ds data
  | TypD _ | DatD _ | SigD _ -> data

and data_mod ctxt m data =
  match m.it with
  | VarM _ -> data
  | StrM ds -> data_list data_dec ctxt ds data
  | FunM (_, _, m1) | AnnotM (m1, _) -> data_mod ctxt m1 data
  | AppM (m1, m2) -> data_list data_mod ctxt [m1; m2] data
  | UnpackM (e, _) -> data_exp ctxt e data
  | LetM (ds, m2) -> data_mod ctxt m2 (data_list data_dec ctxt ds data)

let data_prog ctxt p =
  let Prog (_, ds) = p.it in
  data_list data_dec ctxt ds ""


(* Coercions *)

let rec compile_coerce ctxt src dst t at =
  if src <> dst then
  let emit ctxt = List.iter (emit_instr ctxt at) in
  let non_null n1 n2 =
    if n1 = Null && n2 = Nonull then emit ctxt W.[ref_as_non_null] in
  match src, dst with
  | BlockRep _, DropRep when T.eq t (T.Tup []) ->
    ()
  | _, DropRep ->
    emit ctxt W.[
      drop;
    ]
  | _, BlockRep _ when T.eq t (T.Tup []) ->
    emit ctxt W.[
      drop;
    ]
  | BlockRep _, _ when T.eq t (T.Tup []) ->
    emit ctxt W.[
      i32_const (0l @@ at);
      i31_new;
    ]
  | (BlockRep n1 | BoxedRep n1 | BoxedAbsRep n1), BoxedAbsRep n2
  | (BlockRep n1 | BoxedRep n1), (BlockRep n2 | BoxedRep n2) ->
    non_null n1 n2
  | BoxedAbsRep n1, (BlockRep n2 | BoxedRep n2) ->
    (match T.norm t with
    | T.Bool | T.Byte | T.Int ->
      emit ctxt W.[
        ref_as_i31;
      ]
    | T.Float ->
      let boxedfloat = lower_var_type ctxt at T.Float in
      let rttidx = lower_rtt_global ctxt at boxedfloat in
      emit ctxt W.[
        ref_as_data;
        global_get (rttidx @@ at);
        ref_cast;
      ]
    | T.Tup [] | T.Var _ | T.Data _ ->
      non_null n1 n2
    | T.Fun (_, _, {contents = T.KnownArity _}) as t ->
      let x = lower_var_type ctxt at t in
      let rttidx = lower_rtt_global ctxt at x in
      non_null n1 n2;
      emit ctxt W.[
        ref_as_data;
        global_get (rttidx @@ at);
        ref_cast;
      ]
    | t ->
      (* No types handled here can use super RTTs *)
      let x = lower_var_type ctxt at t in
      let rttidx = lower_rtt_global ctxt at x in
      non_null n1 n2;
      emit ctxt W.[
        ref_as_data;
        global_get (rttidx @@ at);
        ref_cast;
      ]
    )
  | (BlockRep n1 | BoxedRep n1 | BoxedAbsRep n1), (UnboxedRep n2 | UnboxedLaxRep n2) ->
    compile_coerce ctxt src (BoxedRep n2) t at;
    (match T.norm t with
    | T.Bool | T.Byte ->
      emit ctxt W.[
        i31_get_u;
      ]
    | T.Int ->
      emit ctxt W.[
        i31_get_s;
      ]
    | T.Float ->
      let boxedfloat = lower_var_type ctxt at T.Float in
      emit ctxt W.[
        struct_get (boxedfloat @@ at) (0l @@ at);
      ]
    | _ -> ()
    )
  | (UnboxedRep n1 | UnboxedLaxRep n1), (BlockRep n2 | BoxedRep n2 | BoxedAbsRep n2) ->
    (match T.norm t with
    | T.Bool | T.Byte | T.Int ->
      emit ctxt W.[
        i31_new;
      ]
    | T.Float ->
      let boxedfloat = lower_var_type ctxt at T.Float in
      let rttidx = lower_rtt_global ctxt at boxedfloat in
      emit ctxt W.[
        global_get (rttidx @@ at);
        struct_new (boxedfloat @@ at);
      ]
    | _ -> non_null n1 n2
    )
  | UnboxedLaxRep n1, UnboxedRep n2 ->
    (match T.norm t with
    | T.Int ->
      emit ctxt W.[
        i32_const (1l @@ at);
        i32_shl;
        i32_const (1l @@ at);
        i32_shr_s;
      ]
    | T.Bool | T.Byte | T.Float -> ()
    | t -> non_null n1 n2
    )
  | (UnboxedRep n1 | UnboxedLaxRep n1), (UnboxedRep n2 | UnboxedLaxRep n2) ->
    (match T.norm t with
    | T.Bool | T.Byte | T.Int | T.Float -> ()
    | t -> non_null n1 n2
    )
  | DropRep, _ -> assert false


(* Literals *)

let compile_lit ctxt l at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match l with
  | BoolL b ->
    emit ctxt W.[
      i32_const ((if b then 1l else 0l) @@ at);
    ]
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


(* Variables and Paths *)

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
  let loc, funcloc_opt = find_var ctxt x ctxt.ext.envs in
  (match loc with
  | PreLoc idx ->
    let _, l = List.nth Prelude.vals (Int32.to_int idx) in
    compile_lit ctxt l x.at
  | LocalLoc idx ->
    emit_instr ctxt x.at W.(local_get (idx @@ x.at));
  | GlobalLoc idx ->
    emit_instr ctxt x.at W.(global_get (idx @@ x.at));
  | ClosureLoc (null, idx, localidx, typeidx) ->
    emit_instr ctxt x.at W.(local_get (localidx @@ x.at));
    emit_instr ctxt x.at W.(struct_get (typeidx @@ x.at) (idx @@ x.at));
    if null = Null then emit_instr ctxt x.at W.ref_as_non_null
  );
  loc, funcloc_opt

let compile_val_var ctxt x t dst =
  let loc, funcloc_opt = compile_var find_val_var ctxt x in
  let rep = loc_rep loc in
  match funcloc_opt with
  | None -> compile_coerce ctxt rep dst t x.at
  | Some ({typeidx; _} : func_loc) ->
    if null_rep rep = Null && null_rep dst <> Null then
      emit_instr ctxt x.at W.ref_as_non_null

let compile_mod_var ctxt x =
  let loc, _ = compile_var find_mod_var ctxt x in
  if null_rep (loc_rep loc) = Null then emit_instr ctxt x.at W.ref_as_non_null

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
  let t_src = ref T.Bool in
  let found = ref false in
  E.iter_vals (fun x' t' ->
    if not !found then if x' <> x.it then incr i else
      (found := true; t_src := T.as_mono t'.it)
  ) str;
  emit_instr ctxt x.at W.(
    struct_get (typeidx @@ x.at) (int32 (k + !i) @@ x.at)
  );
  if T.eq !t_src t then
    compile_coerce ctxt (struct_rep ()) dst t x.at
  else begin (* one of them will be abstract *)
    compile_coerce ctxt (struct_rep ()) (BoxedAbsRep Nonull) !t_src x.at;
    compile_coerce ctxt (BoxedAbsRep Nonull) dst t x.at
  end

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


let compile_val_var_bind_pre ctxt x t funcloc_opt =
  let scope, env = current_scope ctxt in
  let rep = scope_rep scope in
  let vt =
    match funcloc_opt with
    | None -> lower_value_type ctxt x.at rep t
    | Some ({typeidx; _} : func_loc) ->
      if null_rep rep = Null then W.(ref_null_ typeidx) else W.(ref_ typeidx)
  in
  let loc =
    match scope with
    | PreScope -> assert false
    | LocalScope -> LocalLoc (emit_local ctxt x.at vt)
    | GlobalScope -> GlobalLoc (emit_global ctxt x.at W.Mutable vt None)
  in
  env := E.extend_val !env x (loc, funcloc_opt)

let compile_val_var_bind_post ctxt x t src =
  let _, env = current_scope ctxt in
  let loc, _ = (E.find_val x !env).it in
  compile_coerce ctxt src (loc_rep loc) t x.at;
  (match loc  with
  | PreLoc _ | ClosureLoc _ -> assert false
  | LocalLoc idx -> emit_instr ctxt x.at W.(local_set (idx @@ x.at))
  | GlobalLoc idx -> emit_instr ctxt x.at W.(global_set (idx @@ x.at))
  )

let compile_val_var_bind ctxt x t src funcloc_opt =
  compile_val_var_bind_pre ctxt x t funcloc_opt;
  compile_val_var_bind_post ctxt x t src


let compile_mod_var_bind ctxt x s funcloc_opt =
  let scope, env = current_scope ctxt in
  let _, typeidx = lower_sig_type ctxt x.at s in
  let loc =
    match scope with
    | PreScope -> assert false
    | LocalScope ->
      let idx = emit_local ctxt x.at W.(ref_null_ typeidx) in
      emit_instr ctxt x.at W.(local_set (idx @@ x.at));
      LocalLoc idx
    | GlobalScope ->
      let idx = emit_global ctxt x.at W.Mutable W.(ref_null_ typeidx) None in
      emit_instr ctxt x.at W.(global_set (idx @@ x.at));
      GlobalLoc idx
  in
  env := E.extend_mod !env x (loc, funcloc_opt)


(* Closures *)

let filter_loc ctxt find_var vals =
  Vars.filter (fun x _ ->
    match find_var ctxt Source.(x @@ no_region) ctxt.ext.envs with
    | (PreLoc _ | GlobalLoc _), _ -> false
    | (LocalLoc _ | ClosureLoc _), _ -> true
  ) vals

let filter_vars ctxt vars =
  { vals = filter_loc ctxt find_val_var vars.vals;
    mods = filter_loc ctxt find_mod_var vars.mods;
  }

let compile_load_env ctxt clos closN closNenv vars envflds at =
  if vars <> empty then begin
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let envlocal = emit_local ctxt at W.(ref_null_ closNenv) in
    let rttidx = lower_rtt_global ctxt at closNenv in
    emit ctxt W.[
      local_get (clos @@ at);
      global_get (rttidx @@ at);
      ref_cast;
      local_set (envlocal @@ at);
    ];
    let _, env = current_scope ctxt in
    let clos_mod_env_len =
      Vars.fold (fun x _ i ->
        let idx = clos_env_idx +% i in
        let x' = Source.(@@) x at in
        let _, func_loc_opt = find_mod_var ctxt x' ctxt.ext.envs in
        env := E.extend_mod !env x'
          (ClosureLoc (Nonull, idx, envlocal, closNenv), func_loc_opt);
        i +% 1l
      ) vars.mods 0l
    in
    let _ =
      Vars.fold (fun x _ i ->
        let idx = clos_env_idx +% i in
        let x' = Source.(@@) x at in
        let _, func_loc_opt = find_val_var ctxt x' ctxt.ext.envs in
        let null =
          if func_loc_opt = None then Nonull else
          match List.nth envflds (Int32.to_int i) with
          | W.(FieldType (ValueStorageType (RefType (Nullable, _)), _)) -> Null
          | _ -> Nonull
        in
        env := E.extend_val !env x'
          (ClosureLoc (null, idx, envlocal, closNenv), func_loc_opt);
        i +% 1l
      ) vars.vals clos_mod_env_len
    in ()
  end

let compile_alloc_clos ctxt fn arity vars rec_xs closN closNenv at =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  let rttidx = lower_rtt_global ctxt at closNenv in
  emit_func_ref ctxt at fn;
  emit ctxt W.[
    i32_const (int32 arity @@ at);
    ref_func (fn @@ at);
  ];
  Vars.iter (fun x _ ->
    compile_mod_var ctxt (Source.(@@) x at)
  ) vars.mods;
  Vars.iter (fun x t ->
    let rep = if E.Set.mem x rec_xs then local_rep () else clos_rep () in
    compile_val_var ctxt (Source.(@@) x at) t rep
  ) vars.vals;
  emit ctxt W.[
    global_get (rttidx @@ at);
  ];
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

let rec compile_pat_rec_pre ctxt func_loc_opt p : E.Set.t =
  let t = Source.et p in
  match p.it with
  | WildP -> E.Set.empty
  | VarP x ->
    compile_val_var_bind_pre ctxt x t func_loc_opt;
    E.Set.singleton x.it
  | AnnotP (p1, _) -> compile_pat_rec_pre ctxt func_loc_opt p1
  | LitP _ | TupP _ | ConP _ | RefP _ -> assert false

let rec compile_pat_rec_post ctxt p =
  let t = Source.et p in
  match p.it with
  | WildP -> ()
  | VarP x -> compile_val_var_bind_post ctxt x t (pat_rep ())
  | AnnotP (p1, _) -> compile_pat_rec_post ctxt p1
  | LitP _ | TupP _ | ConP _ | RefP _ -> assert false

let rec compile_pat ctxt fail funcloc_opt p =
  let t = Source.et p in
  let emit ctxt = List.iter (emit_instr ctxt p.at) in
  match p.it with
  | WildP | TupP [] ->
    compile_coerce ctxt (pat_rep ()) DropRep (Source.et p) p.at;

  | LitP l ->
    compile_coerce ctxt (pat_rep ()) rigid_rep t p.at;
    compile_lit ctxt l p.at;
    (match T.norm t with
    | T.Bool | T.Byte | T.Int -> emit ctxt W.[i32_ne]
    | T.Float -> emit ctxt W.[f64_ne]
    | T.Ref _ -> emit ctxt W.[ref_eq; i32_eqz]
    | T.Text ->
      emit ctxt W.[call (intrinsic_text_eq ctxt @@ p.at); i32_eqz]
    | _ -> assert false
    );
    emit ctxt W.[
      br_if (fail @@ p.at);
    ]

  | VarP x ->
    compile_val_var_bind ctxt x t (pat_rep ()) funcloc_opt

  | TupP ps ->
    let typeidx = lower_var_type ctxt p.at t in
    let tmp = emit_local ctxt p.at W.(ref_null_ typeidx) in
    compile_coerce ctxt (pat_rep ()) rigid_rep t p.at;
    emit ctxt W.[
      local_set (tmp @@ p.at);
    ];
    List.iteri (fun i pI ->
      if classify_pat pI > IrrelevantPat then begin
        emit ctxt W.[
          local_get (tmp @@ p.at);
        ];
        emit ctxt W.[
          struct_get (typeidx @@ pI.at) (int32 i @@ pI.at);
        ];
        compile_coerce ctxt field_rep (pat_rep ()) (Source.et pI) pI.at;
        compile_pat ctxt fail None pI;
      end
    ) ps

  | ConP (q, []) ->
    compile_coerce ctxt (pat_rep ()) rigid_rep t p.at;
    (match T.norm t with
    | T.Bool ->
      compile_val_path ctxt q (T.as_mono (Source.et q)) rigid_rep;
      emit ctxt W.[
        i32_ne;
        br_if (fail @@ p.at);
      ]
    | _ ->
      compile_val_path ctxt q (T.as_mono (Source.et q)) ref_rep;
      emit ctxt W.[
        ref_eq;
        i32_eqz;
        br_if (fail @@ p.at);
      ]
    )

  | ConP (q, ps) ->
    (match T.norm t with
    | T.Var (y, _) ->
      let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
      let con = List.assoc (name_of_path q).it data in
      assert (List.length ps = con.arity);
      let bt1 = emit_type ctxt p.at W.(sub [] (func [absref] [dataref])) in
      compile_coerce ctxt (pat_rep ()) rigid_rep t p.at;
      emit_block ctxt p.at W.block W.(typeuse bt1) (fun ctxt ->
        emit ctxt W.[
          br_on_data (0l @@ p.at);
          br (fail +% 1l @@ p.at);
        ]
      );
      let bt2 = emit_type ctxt p.at W.(sub [] (func [dataref] [ref_ con.typeidx])) in
      emit_block ctxt p.at W.block W.(typeuse bt2) (fun ctxt ->
        compile_val_path ctxt q (Source.et p) rigid_rep;
        emit ctxt W.[
          br_on_cast (0l @@ p.at);
          br (fail +% 1l @@ p.at);
        ]
      );
      let tmp = emit_local ctxt p.at W.(ref_null_ con.typeidx) in
      emit ctxt W.[local_tee (tmp @@ p.at)];
      emit ctxt W.[
        struct_get (con.typeidx @@ p.at) (0l @@ p.at);
        i32_const (con.tag @@ p.at);
        i32_ne;
        br_if (fail @@ p.at);
      ];
      List.iteri (fun i pI ->
        if classify_pat pI > IrrelevantPat then begin
          emit ctxt W.[
            local_get (tmp @@ p.at);
            ref_as_non_null;
            struct_get (con.typeidx @@ pI.at) (int32 (i + 1) @@ pI.at);
          ];
          compile_coerce ctxt field_rep (pat_rep ()) (Source.et pI) pI.at;
          compile_pat ctxt fail None pI;
        end
      ) ps
    | _ -> assert false
    )

  | RefP p1 ->
    let typeidx = lower_var_type ctxt p.at t in
    compile_coerce ctxt (pat_rep ()) rigid_rep t p.at;
    emit ctxt W.[
      struct_get (typeidx @@ p.at) (0l @@ p.at);
    ];
    compile_coerce ctxt field_rep (pat_rep ()) (Source.et p1) p1.at;
    compile_pat ctxt fail None p1

  | AnnotP (p1, _) ->
    compile_pat ctxt fail funcloc_opt p1


(* Expressions *)

let rec compile_exp ctxt e dst = ignore (compile_exp_func_opt ctxt e dst)

and compile_exp_func_opt ctxt e dst : func_loc option =
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
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | ConE q ->
    (match T.norm (Source.et e) with
    | T.Bool | T.Var _ ->
      compile_val_path ctxt q (Source.et e) dst;
      None

    | T.Fun _ as t ->
      (* TODO: refactor to avoid duplicating this code *)
      let rec eta t =
        match T.norm t with
        | T.Var (y, _) ->
          let data = find_typ_var ctxt Source.(y @@ q.at) ctxt.ext.envs in
          let con = List.assoc (name_of_path q).it data in
          let _code, clos = lower_func_type ctxt e.at con.arity in
          let argts, argv_opt = lower_param_types ctxt e.at con.arity in
          let fn = emit_func ctxt e.at W.(ref_ clos :: argts) [absref]
            (fun ctxt _ ->
              let ctxt = enter_scope ctxt LocalScope in
              let _clos = emit_param ctxt e.at in
              let args = List.map (fun _ -> emit_param ctxt e.at) argts in
              let arg0 = List.hd args in
              emit ctxt W.[
                i32_const (con.tag @@ q.at);
              ];
              List.iteri (fun i _ ->
                Intrinsic.compile_load_arg ctxt e.at i arg0 argv_opt;
                (* TODO: coerce from local_rep/clos_rep to field_rep here?
                compile_coerce ctxt lax_rep dst (Source.et e) e.at;
                *)
              ) argts;
              compile_val_path ctxt q (T.as_mono (Source.et q)) rigid_rep;
              emit ctxt W.[
                struct_new (con.typeidx @@ e.at);
              ]
            )
          in
          let rttidx = lower_rtt_global ctxt e.at clos in
          emit_func_ref ctxt e.at fn;
          emit ctxt W.[
            i32_const (int32 con.arity @@ e.at);
            ref_func (fn @@ e.at);
            global_get (rttidx @@ e.at);
            struct_new (clos @@ e.at);
          ];
          Some {funcidx = fn; typeidx = clos; arity = con.arity}

        | T.Fun (_, t', _) -> eta t'

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
    compile_exp ctxt e1 lax_rep;
    (match op, T.norm (Source.et e) with
    | PosOp, T.Int -> ()
    | PosOp, T.Float -> ()
    | NegOp, T.Int -> emit ctxt W.[i32_sub]
    | NegOp, T.Float -> emit ctxt W.[f64_neg]
    | InvOp, T.Int -> emit ctxt W.[i32_xor]
    | NotOp, T.Bool -> emit ctxt W.[i32_eqz]
    | _ -> assert false
    );
    compile_coerce ctxt lax_rep dst (Source.et e) e.at;
    None

  | BinE (e1, op, e2) ->
    let src =
      match op with
      | DivOp | ModOp | ShrOp -> rigid_rep
      | _ -> lax_rep
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
      emit ctxt W.[call (intrinsic_text_cat ctxt @@ e.at)]
    | _ -> assert false
    );
    compile_coerce ctxt lax_rep dst (Source.et e) e.at;
    None

  | RelE (e1, op, e2) ->
    compile_exp ctxt e1 rigid_rep;
    compile_exp ctxt e2 rigid_rep;
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
      emit ctxt W.[call (intrinsic_text_eq ctxt @@ e.at)]
    | NeOp, T.Text ->
      emit ctxt W.[call (intrinsic_text_eq ctxt @@ e.at); i32_eqz]
    | _ -> assert false
    );
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | LogE (e1, AndThenOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
      emit ctxt W.[
        i32_const (0l @@ e1.at);
      ];
      compile_exp ctxt e1 rigid_rep;
      emit ctxt W.[
        i32_eqz;
        br_if (0l @@ e.at);
        drop;
      ];
      compile_exp ctxt e2 rigid_rep;
    );
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | LogE (e1, OrElseOp, e2) ->
    emit_block ctxt e.at W.block W.(result i32) (fun ctxt ->
      emit ctxt W.[
        i32_const (1l @@ e1.at);
      ];
      compile_exp ctxt e1 rigid_rep;
      emit ctxt W.[
        br_if (0l @@ e.at);
        drop;
      ];
      compile_exp ctxt e2 rigid_rep;
    );
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | RefE e1 ->
    let typeidx = lower_var_type ctxt e.at (Source.et e) in
    let rttidx = lower_rtt_global ctxt e.at typeidx in
    compile_exp ctxt e1 field_rep;
    emit ctxt W.[
      global_get (rttidx @@ e.at);
      struct_new (typeidx @@ e.at);
    ];
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | DerefE e1 ->
    let typ = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1 rigid_rep;
    emit ctxt W.[
      struct_get (typ @@ e.at) (0l @@ e.at);
    ];
    compile_coerce ctxt field_rep dst (Source.et e) e.at;
    None

  | AssignE (e1, e2) ->
    let typ = lower_var_type ctxt e.at (Source.et e1) in
    compile_exp ctxt e1 rigid_rep;
    compile_exp ctxt e2 field_rep;
    emit ctxt W.[
      struct_set (typ @@ e.at) (0l @@ e.at);
    ];
    compile_coerce ctxt unit_rep dst (Source.et e) e.at;
    None

  | TupE [] ->
    compile_coerce ctxt unit_rep dst (Source.et e) e.at;
    None

  | TupE es ->
    let typ = lower_var_type ctxt e.at (Source.et e) in
    let rttidx = lower_rtt_global ctxt e.at typ in
    List.iter (fun e -> compile_exp ctxt e field_rep) es;
    emit ctxt W.[
      global_get (rttidx @@ e.at);
      struct_new (typ @@ e.at);
    ];
    compile_coerce ctxt rigid_rep dst (Source.et e) e.at;
    None

  | FunE (p1, e2) ->
    Some (compile_func ctxt e)

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
          assert (List.length es = con.arity);
          emit ctxt W.[
            i32_const (con.tag @@ q.at);
          ];
          List.iter (fun e -> compile_exp ctxt e field_rep) es;
          compile_val_path ctxt q (T.as_mono (Source.et q)) rigid_rep;
          emit ctxt W.[
            struct_new (con.typeidx @@ e1.at);
          ];
          compile_coerce ctxt rigid_rep dst (Source.et e) e.at;

        | T.Fun _ ->
          compile_exp ctxt e1 rigid_rep;
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt (List.nth es i) arg_rep
          );
          emit ctxt W.[
            call (intrinsic_func_apply (List.length es) ctxt @@ e.at);
          ];
          compile_coerce ctxt arg_rep dst (Source.et e) e.at;

        | _ ->
          assert false
        )

      | _ ->
        (match compile_exp_func_opt ctxt e1 rigid_rep with
        | Some {funcidx; arity; _} when arity = List.length es ->
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt (List.nth es i) arg_rep
          );
          emit ctxt W.[
            call (funcidx @@ e.at);
          ]
        | _ ->
          Intrinsic.compile_push_args ctxt e.at (List.length es) 0l (fun i ->
            compile_exp ctxt (List.nth es i) arg_rep
          );
          emit ctxt W.[
            call (intrinsic_func_apply (List.length es) ctxt @@ e.at);
          ]
        );
        compile_coerce ctxt arg_rep dst (Source.et e) e.at
    in flat e1 [e2];
    None

  | AnnotE (e1, _t) ->
    compile_exp_func_opt ctxt e1 dst

  | IfE (e1, e2, e3) ->
    let bt = lower_block_type ctxt e.at dst (Source.et e) in
    emit_block ctxt e.at W.block bt (fun ctxt ->
      emit_block ctxt e.at W.block W.void (fun ctxt ->
        compile_exp ctxt e1 rigid_rep;
        emit ctxt W.[
          i32_eqz;
          br_if (0l @@ e.at);
        ];
        compile_exp ctxt e2 dst;
        emit ctxt W.[
          br (1l @@ e.at);
        ];
      );
      compile_exp ctxt e3 dst;
    );
    None

  | CaseE (e1, []) ->
    compile_exp ctxt e1 (pat_rep ());
    emit ctxt W.[
      unreachable;
    ];
    None

  | CaseE (e1, pes) ->
    let t1 = Source.et e1 in
    let tmp = emit_local ctxt e1.at (lower_value_type ctxt e1.at (tmp_rep ()) t1) in
    compile_exp ctxt e1 (tmp_rep ());
    emit ctxt W.[
      local_set (tmp @@ e1.at);
    ];
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
            compile_coerce ctxt (tmp_rep ()) (pat_rep ()) (Source.et pI) e.at;
            compile_pat ctxt (-1l) None pI;
            compile_exp ctxt eI dst;
            emit ctxt W.[br (0l @@ eI.at)];
            false
          | PartialPat ->
            let ctxt = enter_scope ctxt LocalScope in
            emit_block ctxt pI.at W.block W.void (fun ctxt ->
              emit ctxt W.[local_get (tmp @@ pI.at)];
              compile_coerce ctxt (tmp_rep ()) (pat_rep ()) t1 e.at;
              compile_pat ctxt 0l None pI;
              compile_exp ctxt eI dst;
              emit ctxt W.[br (1l @@ eI.at)];
            );
            true
        ) true pes
      in
      if ends_with_partial then emit ctxt W.[unreachable]
    );
    None

  | PackE (m, s) ->
    compile_mod ctxt m;
    compile_coerce_mod ctxt (Source.et m) (Source.et s) e.at;
    None

  | LetE (ds, e1) ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs ctxt ds unit_rep;
    compile_exp_func_opt ctxt e1 dst


and compile_func ctxt e : func_loc =
  let func_loc, def, _fixup = compile_func_staged ctxt E.Set.empty e in
  def ctxt;
  func_loc

and compile_func_staged ctxt rec_xs f : func_loc * _ * _ =
  let emit ctxt = List.iter (emit_instr ctxt f.at) in
  let vars = filter_vars ctxt (free_exp f) in
  let rec flat ps e =
    match e.it with
    | FunE (p, e') -> flat (p::ps) e'
    | _ ->
      let fn, def_func = emit_func_deferred ctxt f.at in
      let envflds, fixups = lower_clos_env ctxt f.at vars rec_xs in
      let ps = List.rev ps in
      let arity = List.length ps in
      let _code, closN, closNenv = lower_clos_type ctxt f.at arity envflds in
      let def ctxt =
        let argts, argv_opt = lower_param_types ctxt f.at arity in
        def_func ctxt W.(ref_ closN :: argts) [absref] (fun ctxt _ ->
          let ctxt = enter_scope ctxt LocalScope in
          let clos = emit_param ctxt f.at in
          let args = List.map (fun _ -> emit_param ctxt f.at) argts in
          let arg0 = List.hd args in
          compile_load_env ctxt clos closN closNenv vars envflds f.at;

          let partial = List.exists (fun p -> classify_pat p = PartialPat) ps in
          if not partial then
            List.iteri (fun i pI ->
              match classify_pat pI with
              | IrrelevantPat -> ()
              | TotalPat ->
                Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                compile_pat ctxt (-1l) None pI
              | PartialPat -> assert false
            ) ps
          else
            emit_block ctxt f.at W.block W.void (fun ctxt ->
              emit_block ctxt f.at W.block W.void (fun ctxt ->
                List.iteri (fun i pI ->
                  match classify_pat pI with
                  | IrrelevantPat -> ()
                  | TotalPat ->
                    Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                    compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                    compile_pat ctxt (-1l) None pI
                  | PartialPat ->
                    Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                    compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                    compile_pat ctxt 0l None pI;
                ) ps;
                emit ctxt W.[br (1l @@ f.at)];
              );
              emit ctxt W.[unreachable]
            );
          compile_exp ctxt e arg_rep
        );
        compile_alloc_clos
          ctxt fn (List.length ps) vars rec_xs closN closNenv f.at
      in
      let fixup ctxt self =
        if fixups <> [] then begin
          let tmp = emit_local ctxt f.at W.(ref_null_ closNenv) in
          let rttidx = lower_rtt_global ctxt f.at closNenv in
          compile_val_var ctxt Source.(self @@ f.at) (Source.et f) ref_rep;
          emit ctxt W.[
            ref_as_data;
            global_get (rttidx @@ f.at);
            ref_cast;
            local_set (tmp @@ f.at);
          ];
          List.iter (fun (x, t, i) ->
            emit ctxt W.[local_get (tmp @@ f.at)];
            compile_val_var ctxt Source.(x @@ f.at) t (clos_rep ());
            emit ctxt W.[
              struct_set (closNenv @@ f.at) (clos_env_idx +% int32 i @@ f.at)
            ];
          ) fixups
        end
      in
      {funcidx = fn; typeidx = closN; arity = List.length ps}, def, fixup
  in flat [] f


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
    compile_decs ctxt ds unit_rep;
    let vars = Syntax.list bound_dec ds in
    let _, str = lower_sig_type ctxt m.at (Source.et m) in
    Vars.iter (fun x _ ->
      compile_mod_var ctxt Source.(x @@ m.at)
    ) vars.mods;
    Vars.iter (fun x t ->
      compile_val_var ctxt Source.(x @@ m.at) t (struct_rep ())
    ) vars.vals;
    let rttidx = lower_rtt_global ctxt m.at str in
    emit ctxt W.[
      global_get (rttidx @@ m.at);
      struct_new (str @@ m.at);
    ];
    None

  | FunM (x, _s, m2) ->
    let vars = filter_vars ctxt (free_mod m) in
    let envflds, _ = lower_clos_env ctxt m.at vars E.Set.empty in
    let _, s1, s2 = T.as_fct (Source.et m) in
    let _code, closN, closNenv = lower_fct_clos_type ctxt m.at s1 s2 envflds in
    let vt1, _ = lower_sig_type ctxt x.at s1 in
    let vt2, _ = lower_sig_type ctxt m2.at s2 in
    let fn = emit_func ctxt m.at W.(ref_ closN :: [vt1]) [vt2]
      (fun ctxt _ ->
        let ctxt = enter_scope ctxt LocalScope in
        let _, env = current_scope ctxt in
        let clos = emit_param ctxt m2.at in
        let arg = emit_param ctxt m2.at in
        compile_load_env ctxt clos closN closNenv vars envflds m2.at;
        env := E.extend_mod !env x (LocalLoc arg, None);
        compile_mod ctxt m2
      )
    in
    compile_alloc_clos ctxt fn 1 vars E.Set.empty closN closNenv m.at;
    Some {funcidx = fn; typeidx = closN; arity = 1}

  | AppM (m1, m2) ->
    let _, clos1 = lower_sig_type ctxt m1.at (Source.et m1) in
    let _, s11, s12 = T.as_fct (Source.et m1) in
    let func_loc_opt = compile_mod_func_opt ctxt m1 in
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
    compile_coerce_mod ctxt s12 (Source.et m) m.at;
    None

  | AnnotM (m1, _s) ->
    compile_mod ctxt m1;
    compile_coerce_mod ctxt (Source.et m1) (Source.et m) m.at;
    None

  | UnpackM (e, _s) ->
    compile_exp ctxt e (UnboxedRep Nonull);
    None

  | LetM (ds, m1) ->
    let ctxt = enter_scope ctxt LocalScope in
    compile_decs ctxt ds unit_rep;
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
      E.iter_vals (fun x t ->
        emit_instr ctxt at W.(local_get (tmp @@ at));
        compile_val_proj ctxt str1 (Source.(@@) x at)
          (T.as_mono t.it) (struct_rep ());
      ) str2;
      let rttidx = lower_rtt_global ctxt at typeidx2 in
      emit ctxt W.[
        global_get (rttidx @@ at);
        struct_new (typeidx2 @@ at);
      ];

    | T.Fct (_, s11, s12), T.Fct (_, s21, s22) ->
      let ft, fidx = lower_sig_type ctxt at s1 in
      let envflds = W.[field ft] in
      let _code, clos1, closenv = lower_fct_clos_type ctxt at s21 s22 envflds in
      let vt21, _ = lower_sig_type ctxt at s21 in
      let vt22, _ = lower_sig_type ctxt at s22 in
      let fn = emit_func ctxt at W.(ref_ clos1 :: [vt21]) [vt22]
        (fun ctxt _ ->
          let clos = emit_param ctxt at in
          let arg = emit_param ctxt at in
          let tmp = emit_local ctxt at W.(ref_null_ fidx) in
          let rttidx = lower_rtt_global ctxt at closenv in
          emit ctxt W.[
            local_get (clos @@ at);
            global_get (rttidx @@ at);
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
      let rttidx = lower_rtt_global ctxt at closenv in
      emit_func_ref ctxt at fn;
      emit ctxt W.[
        local_set (tmp @@ at);
        i32_const (1l @@ at);
        ref_func (fn @@ at);
        local_get (tmp @@ at);
        ref_as_non_null;
        global_get (rttidx @@ at);
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
    List.exists2 (fun (x1, t1) (x2, t2) -> need_coerce_val t1.it t2.it)
      (E.vals str1) (E.vals str2) ||
    List.exists2 (fun (x1, s1) (x2, s2) -> need_coerce_mod s1.it s2.it)
      (E.mods str1) (E.mods str2)
  | T.Fct (_, s11, s12), T.Fct (_, s21, s22) ->
    need_coerce_mod s21 s11 || need_coerce_mod s12 s22 ||
    (* The following would be unnecessary if we had Wasm function subtyping *)
    need_coerce_mod s11 s21 || need_coerce_mod s22 s12
  | _ ->
    assert false

and need_coerce_val t1 t2 =
  match T.norm (T.as_mono t1), T.norm (T.as_mono t2) with
  | (T.Var _ | T.Tup []), (T.Var _ | T.Tup []) -> false
  | T.Var _, _ | _, T.Var _ -> true
  | _, _ -> false


(* Declarations *)

and compile_dec_rec ctxt d : E.Set.t * _ list =
  match d.it with
  | ValD (p, e) ->
    let xs = compile_pat_rec_pre ctxt None p in
    let pass2 ctxt xs = (* knows recursive bindings but not yet func_locs *)
      let func_loc, def, fixup = compile_func_staged ctxt xs e in
      ignore (compile_pat_rec_pre ctxt (Some func_loc) p);
      let pass3 ctxt = (* knows func_locs *)
        def ctxt;
        compile_pat_rec_post ctxt p;
        let pass4 ctxt = (* has the environment initialised, fix up recursion *)
          if xs <> E.Set.empty then
            fixup ctxt (E.Set.choose xs)
        in pass4
      in pass3
    in xs, [pass2]
  | DatD _ ->
    compile_dec ctxt d DropRep;
    E.Set.empty, []
  | RecD ds -> compile_decs_rec ctxt ds
  | _ -> assert false

and compile_decs_rec ctxt ds : E.Set.t * _ list =
  match ds with
  | [] -> E.Set.empty, []
  | d::ds' ->
    let xs1, fs1 = compile_dec_rec ctxt d in
    let xs2, fs2 = compile_decs_rec ctxt ds' in
    E.Set.union xs1 xs2, fs1 @ fs2

and compile_dec ctxt d dst =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
  let scope, env = current_scope ctxt in
  match d.it with
  | ExpD e ->
    compile_exp ctxt e dst

  | AssertD e ->
    compile_exp ctxt e rigid_rep;
    emit ctxt W.[
      i32_eqz;
      if_ W.void [unreachable @@ d.at] [];
    ];
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | ValD (p, e) ->
    (match classify_pat p with
    | IrrelevantPat ->
      compile_exp ctxt e DropRep;
    | TotalPat ->
      let funcloc_opt = compile_exp_func_opt ctxt e (pat_rep ()) in
      compile_pat ctxt (-1l) funcloc_opt p
    | PartialPat ->
      emit_block ctxt e.at W.block W.void (fun ctxt ->
        emit_block ctxt e.at W.block W.void (fun ctxt ->
          let funcloc_opt = compile_exp_func_opt ctxt e (pat_rep ()) in
          compile_pat ctxt 0l funcloc_opt p;
          emit ctxt W.[br (1l @@ d.at)];
        );
        emit ctxt W.[unreachable]
      )
    );
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | TypD _ ->
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | DatD (y, ys, cs) ->
    let t = T.Var (y.it, List.map T.var (List.map Source.it ys)) in
    let data =
      List.mapi (fun i c ->
        let (x, ts) = c.it in
        let ts' = List.map Source.et ts in
        let typeidx = lower_con_type ctxt x.at ts' in
        if ts = [] then
          emit ctxt W.[
            i32_const (int32 i @@ x.at);
            i31_new;
          ]
        else
          emit ctxt W.[
            rtt_canon (typeidx @@ x.at);
          ];
        let t_data = T.Data (T.fun_flat ts' t) in
        compile_val_var_bind ctxt x t_data rigid_rep None;
        (x.it, {tag = int32 i; typeidx; arity = List.length ts})
      ) (List.sort (fun c1 c2 -> compare c1.it c2.it) cs)
    in env := E.extend_typ !env y data;
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | ModD (x, m) ->
    let funcloc_opt = compile_mod_func_opt ctxt m in
    compile_mod_var_bind ctxt x (Source.et m) funcloc_opt;
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | SigD _ ->
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

  | RecD ds ->
    let xs, passes2 = compile_decs_rec ctxt ds in
    let passes3 = List.map (fun f -> f ctxt xs) passes2 in
    let passes4 = List.map (fun f -> f ctxt) passes3 in
    List.iter (fun f -> f ctxt) passes4

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
      compile_val_proj ctxt str x t (struct_rep ());
      compile_val_var_bind ctxt x t (struct_rep ()) None
    ) str;
    compile_coerce ctxt unit_rep dst (T.Tup []) d.at

and compile_decs ctxt ds dst =
  match ds with
  | [] ->
    compile_coerce ctxt unit_rep dst (T.Tup []) Source.no_region
  | [d] ->
    compile_dec ctxt d dst
  | d::ds' ->
    compile_dec ctxt d DropRep;
    compile_decs ctxt ds' dst


(* Programs *)

let compile_imp_pre ctxt d =
  let ImpD (x, url) = d.it in
  let str = Source.et d in
  E.iter_mods (fun x' s ->
    let _, typeidx = lower_sig_type ctxt s.at s.it in
    let vt = W.ref_null_ typeidx in
    ignore (emit_global_import ctxt s.at url ("module " ^ x') W.Mutable vt)
  ) str;
  E.iter_vals (fun x' pt ->
    let t = T.as_mono pt.it in
    let vt = lower_value_type ctxt pt.at (global_rep ()) t in
    ignore (emit_global_import ctxt pt.at url x' W.Mutable vt)
  ) str

let compile_imp ctxt idx d =
  let ImpD (x, url) = d.it in
  let str = Source.et d in
  E.iter_mods (fun _ s ->
    emit_instr ctxt s.at W.(global_get (int32 !idx @@ s.at)); incr idx;
    emit_instr ctxt s.at W.(ref_as_non_null);
  ) str;
  E.iter_vals (fun _ pt ->
    emit_instr ctxt pt.at W.(global_get (int32 !idx @@ pt.at)); incr idx;
    compile_coerce ctxt (global_rep ()) (struct_rep ()) (T.as_mono pt.it) pt.at
  ) str;
  let vt, typeidx = lower_str_type ctxt x.at str in
  let rttidx = lower_rtt_global ctxt d.at typeidx in
  emit_instr ctxt d.at W.(global_get (rttidx @@ d.at));
  emit_instr ctxt d.at W.(struct_new (typeidx @@ d.at));
  compile_mod_var_bind ctxt x (T.Str ([], str)) None

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
  let data = if !Flags.headless then "" else data_prog ctxt p in
  let t, _ = Source.et p in
  let vt = lower_value_type ctxt p.at (global_rep ()) t in
  let start_idx =
    emit_func ctxt p.at [] [] (fun ctxt _ ->
      List.iter (compile_imp_pre ctxt) is;
      if data <> "" then begin
        let seg = emit_passive_data ctxt p.at data in
        let len = int32 (String.length data) in
        let dataidx = emit_global ctxt p.at W.Mutable W.i32 None in
        ctxt.ext.data := dataidx;
        List.iter (emit_instr ctxt p.at) W.[
          i32_const (len @@ p.at);
          call (Runtime.import_mem_alloc ctxt @@ p.at);
          global_set (dataidx @@ p.at);
          global_get (dataidx @@ p.at);
          i32_const (0l @@ p.at);
          i32_const (len @@ p.at);
          memory_init (seg @@ p.at);
        ]
      end;
      List.iter (compile_imp ctxt (ref 0)) is;
      compile_decs ctxt ds (global_rep ());
      let result_idx = emit_global ctxt p.at W.Mutable vt None in
      emit_instr ctxt p.at W.(global_set (result_idx @@ p.at));
      emit_global_export ctxt p.at "return" result_idx;
    )
  in
  emit_start ctxt p.at start_idx;
  let _, env = current_scope ctxt in
  E.iter_mods (fun x' locs ->
    let (loc, funcloc_opt) = locs.it in
    emit_global_export ctxt locs.at ("module " ^ x') (as_global_loc loc);
    Option.iter (fun {funcidx; _} ->
      emit_func_export ctxt locs.at ("func module " ^ x') funcidx) funcloc_opt
  ) !env;
  E.iter_vals (fun x' locs ->
    let (loc, funcloc_opt) = locs.it in
    emit_global_export ctxt locs.at x' (as_global_loc loc);
    Option.iter (fun {funcidx; _} ->
      emit_func_export ctxt locs.at ("func " ^ x') funcidx) funcloc_opt
  ) !env;
  Emit.gen_module ctxt p.at
