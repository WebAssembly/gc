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

let nyi at s = raise (NYI (at, s))


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
  E.iter_vals (fun x sl -> let s, l = sl.it in
    Printf.printf " %s(%s)=%s" (string_of_sort s) x (string_of_loc l)) env;
  Printf.printf "\n"

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

let compile_var ctxt x t dst =
  let loc, _ = find_val_var ctxt x ctxt.ext.envs in
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
  compile_coerce ctxt (loc_rep loc) dst t x.at

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

let rec compile_pat pass ctxt fail p =
  let t = Source.et p in
  let t' = lower_value_type ctxt p.at pat_rep t in
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

  | VarP x when pass = RecPrePass ->
    let scope, env = current_scope ctxt in
    let loc =
      match scope with
      | PreScope -> assert false
      | LocalScope | FuncScope | ModuleScope ->
        LocalLoc (emit_local ctxt x.at t')
      | GlobalScope ->
        let const = default_const ctxt x.at (loc_rep (GlobalLoc 0l)) t in
        GlobalLoc (emit_global ctxt x.at W.Mutable t' const)
    in
    env := E.extend_val !env x (loc, None)

  | VarP x when pass = RecPass ->
    let _, env = current_scope ctxt in
    let loc, _ = (E.find_val x !env).it in
    compile_coerce ctxt pat_rep (loc_rep loc) t x.at;
    (match loc  with
    | PreLoc _ | ClosureLoc _ -> assert false
    | LocalLoc idx -> emit ctxt W.[local_set (idx @@ p.at)]
    | GlobalLoc idx -> emit ctxt W.[global_set (idx @@ p.at)]
    )

  | VarP x ->
    compile_pat RecPrePass ctxt fail p;
    compile_pat RecPass ctxt fail p

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
    compile_path ctxt q (Source.et p) BoxedRep;
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
      let bt1 = emit_type ctxt p.at W.(type_func [eqref] [dataref]) in
      emit_block ctxt p.at W.block W.(typeuse bt1) (fun ctxt ->
        emit ctxt W.[
          br_on_data (0l @@ p.at);
          br (fail +% 1l @@ p.at);
        ]
      );
      let bt2 = emit_type ctxt p.at W.(type_func [dataref] [ref_ con.typeidx]) in
      emit_block ctxt p.at W.block W.(typeuse bt2) (fun ctxt ->
        compile_path ctxt q (Source.et p) BoxedRep;
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
    compile_var ctxt x (Source.et e) dst;
    let _, func_loc_opt = find_val_var ctxt x ctxt.ext.envs in
    func_loc_opt

  | VarE q ->
    compile_path ctxt q (Source.et e) dst;
    None

  | LitE l ->
    compile_lit ctxt l e.at;
    compile_coerce ctxt UnboxedRigidRep dst (Source.et e) e.at;
    None

  | ConE q ->
    (match T.norm (Source.et e) with
    | T.Var (y, _) ->
      compile_path ctxt q (Source.et e) dst;
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
          let fn = emit_func ctxt e.at W.(ref_ clos :: argts) W.[eqref]
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
              compile_path ctxt q (Source.et e) BoxedRep;
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
        let vars = free_exp e in
        let free_vals =
          List.filter_map (fun x ->
            let x' = Source.(x @@ e2.at) in
            let locs = find_val_var ctxt x' ctxt.ext.envs in
            match fst locs with
            | PreLoc _ | GlobalLoc _ -> None
            | LocalLoc _ | ClosureLoc _ -> Some (x', locs)
          ) (Vars.elements vars.vals)
        in
        let free_mods =
          List.filter_map (fun x ->
            let x' = Source.(x @@ e2.at) in
            let locs = find_mod_var ctxt x' ctxt.ext.envs in
            match fst locs with
            | PreLoc _ | GlobalLoc _ -> None
            | LocalLoc _ | ClosureLoc _ -> Some (x', locs)
          ) (Vars.elements vars.mods)
        in
        let envts = List.map (fun _ -> W.eqref) (free_vals @ free_mods) in
        let ps = List.rev ps in
        let arity = List.length ps in
        let anyclos = lower_anyclos_type ctxt e.at in
        let _code, closN, closNenv = lower_clos_type ctxt e.at arity envts in
        let argts, argv_opt = lower_param_types ctxt e.at arity in
        let fn = emit_func ctxt e.at W.(ref_ closN :: argts) W.[eqref]
          (fun ctxt _ ->
            let ctxt = enter_scope ctxt FuncScope in
            let clos = emit_param ctxt e2.at in
            let args = List.map (fun _ -> emit_param ctxt e2.at) argts in
            let arg0 = List.hd args in

            let envlocal =
              if envts = [] then 0l else
              let envlocal = emit_local ctxt e2.at W.(ref_null_ closNenv) in
              emit ctxt W.[
                local_get (clos @@ e2.at);
                rtt_canon (anyclos @@ e2.at);
                rtt_sub (closN @@ e2.at);
                rtt_sub (closNenv @@ e2.at);
                ref_cast;
                local_set (envlocal @@ e2.at);
              ];
              envlocal
            in
            let _, env = current_scope ctxt in
            List.iteri (fun i (x, (loc, func_loc_opt)) ->
              let idx = clos_env_idx +% int32 i in
              env := E.extend_val !env x
                (ClosureLoc (idx, envlocal, closNenv), func_loc_opt)
            ) free_vals;
            let clos_mod_env_idx = clos_env_idx +% int32 (List.length free_vals) in
            List.iteri (fun i (x, (loc, func_loc_opt)) ->
              let idx = clos_mod_env_idx +% int32 i in
              env := E.extend_mod !env x
                (ClosureLoc (idx, envlocal, closNenv), func_loc_opt)
            ) free_mods;

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
        emit_func_ref ctxt e.at fn;
        emit ctxt W.[
          i32_const (int32 (List.length ps) @@ e.at);
          ref_func (fn @@ e.at);
        ];
        List.iteri (fun i (x, _) ->
(*TODO*)
          compile_var ctxt x (T.Tup []) (loc_rep (ClosureLoc (0l, 0l, 0l)));
        ) free_vals;
        List.iteri (fun i (x, _) ->
          nyi x.at "closing over non-global modules"
          (*compile_mod_var ctxt x t clos_rep;*)
        ) free_mods;
        emit ctxt W.[
          rtt_canon (anyclos @@ e.at);
          rtt_sub (closN @@ e.at);
        ];
        if envts <> [] then
          emit ctxt W.[
            rtt_sub (closNenv @@ e.at);
          ];
        emit ctxt W.[
          struct_new (closNenv @@ e.at);
        ];
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
          compile_path ctxt q (Source.et e1) BoxedRep;
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


(* Declarations *)

and compile_dec pass ctxt d dst =
  let emit ctxt = List.iter (emit_instr ctxt d.at) in
(*
  let scope, env = current_scope ctxt in
*)
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
    let scope, env = current_scope ctxt in
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
    let scope, env = current_scope ctxt in
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

  | ModD _ ->
    nyi d.at "module definitions"

  | SigD _ ->
    ()

  | RecD ds when pass <> FullPass ->
    compile_decs pass ctxt ds

  | RecD ds ->
    compile_decs RecPrePass ctxt ds;
    compile_decs RecPass ctxt ds

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
      in env := E.extend_val !env x' (sort, LocalLoc idx)
  ) xs (Source.et d)
*)

let compile_prog p : W.module_ =
  let Prog (is, ds) = p.it in
  let ctxt = enter_scope (make_ctxt ()) GlobalScope in
(*
  List.iter (compile_imp ctxt) is;
*)
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
