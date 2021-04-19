open Source
open Syntax
open Emit

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

type loc =
  | DirectLoc of int32

type func_loc = {funcidx : int32; arity : int}

type data_con = {tag : int32; typeidx : int32; flds : T.typ list}
type data = (string * data_con) list
type env = (loc * func_loc option, data, loc, unit) E.env
type scope = PreScope | LocalScope | GlobalScope | ModuleScope

let make_env () =
  let env = ref Env.empty in
  List.iteri (fun i (x, _) ->
    env := E.extend_val !env Source.(x @@ Prelude.region)
      (DirectLoc (int32 i), None)
  ) Prelude.vals;
  env

type pass = FullPass | RecPrePass | RecPass


(* Compilation context *)

type ctxt_ext = { envs : (scope * env ref) list }
type ctxt = ctxt_ext Emit.ctxt

let make_ext_ctxt () : ctxt_ext = {envs = [(PreScope, make_env ())]}
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

let max_func_arity = 5

let scope_rep = function
  | PreScope -> UnboxedRigidRep
  | LocalScope | ModuleScope | GlobalScope -> BoxedRep

let is_boxed_rep = function
  | BlockRep | BoxedRep -> true
  | _ -> false

let rec lower_value_type ctxt at rep t : W.value_type =
  if is_boxed_rep rep then W.(RefType (Nullable, EqHeapType)) else
  match T.norm t with
  | T.Bool | T.Byte | T.Int -> W.i32
  | T.Float -> W.f64
  | t -> W.(ref_null_heap (lower_heap_type ctxt at t))

and lower_heap_type ctxt at t : W.heap_type =
  match T.norm t with
  | T.Var _ -> W.eq
  | T.Bool | T.Byte | T.Int -> W.i31
  | T.Tup [] -> W.eq
  | t -> W.(type_ (lower_var_type ctxt at t))

and lower_var_type ctxt at t : int32 =
  match T.norm t with
  | T.Float ->
    emit_type ctxt at W.(type_struct [field f64])
  | T.Text ->
    emit_type ctxt at W.(type_array (field_mut_pack i8))
  | T.Tup ts ->
    let ts = List.map (lower_value_type ctxt at BoxedRep) ts in
    emit_type ctxt at W.(type_struct (List.map W.field ts))
  | T.Ref t1 ->
    let t1' = lower_value_type ctxt at BoxedRep t1 in
    emit_type ctxt at W.(type_struct [field_mut t1'])
  | T.Fun _ ->
    lower_anyclos_type ctxt at
  | _ -> Printf.printf "%s\n%!" (T.string_of_typ t); assert false

and lower_anyclos_type ctxt at : int32 =
  emit_type ctxt at W.(type_struct [field i32])

and lower_func_type ctxt at arity : int32 * int32 =
  let code, def_code = emit_type_deferred ctxt at in
  let closdt = W.(type_struct [field i32; field (ref_ code)]) in
  let clos = emit_type ctxt at closdt in
  let argts, _ = lower_param_types ctxt at arity in
  let codedt = W.(type_func (ref_ clos :: argts) [eqref]) in
  def_code codedt;
  code, clos

and lower_clos_type ctxt at arity envts : int32 * int32 =
  let code, _ = lower_func_type ctxt at arity in
  let closdt =
    W.(type_struct (field i32 :: field (ref_ code) :: List.map field envts)) in
  let clos = emit_type ctxt at closdt in
  code, clos

and lower_param_types ctxt at arity : W.value_type list * int32 option =
  if arity <= max_func_arity then
    List.init arity (fun _ -> W.eqref), None
  else
    let argv = emit_type ctxt at W.(type_array (field_mut eqref)) in
    W.[ref_ argv], Some argv

and lower_block_type ctxt at rep t : W.block_type =
  match t with
  | T.Tup [] when rep = BlockRep -> W.void
  | t -> W.result (lower_value_type ctxt at rep t)

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


(* Application and combinators *)

let clos_arity_idx = 0l
let clos_code_idx = 1l
let clos_env_idx = 2l  (* first environment entry *)
let curry_fun_idx = clos_env_idx
let curry_arg_idx = clos_env_idx +% 1l  (* first argument or argv *)

let compile_args ctxt at shift n compile_eI =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match lower_param_types ctxt at n with
  | _, None ->
    for i = 0 to n - 1 do
      compile_eI i
    done
  | _, Some argv ->
    let tmp = emit_local ctxt at W.(ref_null_ argv) in
    emit ctxt W.[
      i32_const (int32 n @@ at);
      rtt_canon (argv @@ at);
      array_new_default (argv @@ at);
      local_tee (tmp +% shift @@ at);
      ref_as_non_null;
    ];
    for i = 0 to n - 1 do
      emit ctxt W.[
        local_get (tmp +% shift @@ at);
        i32_const (int32 i @@ at);
      ];
      compile_eI i;
      emit ctxt W.[
        array_set (argv @@ at);
      ]
    done

let compile_load_arg ctxt at arg0 i argv_opt =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match argv_opt with
  | None ->
    assert (i < max_func_arity);
    emit ctxt W.[
      local_get (arg0 +% int32 i @@ at);
    ]
  | Some argv ->
    emit ctxt W.[
      local_get (arg0 @@ at);
      i32_const (int32 i @@ at);
      array_get (argv @@ at);
    ]

let compile_load_args ctxt at shift arg0 i j src_argv_opt =
  assert (j <= max_func_arity || src_argv_opt <> None);
  if j - i > max_func_arity && i = 0 then
    (* Reuse argv *)
    emit_instr ctxt at W.(local_get (arg0 @@ at))
  else
    compile_args ctxt at shift (j - i) (fun k ->
      compile_load_arg ctxt at arg0 (i + k) src_argv_opt
    )

let rec compile_apply ctxt at arity =
  Emit.lookup_intrinsic ctxt ("apply" ^ string_of_int arity) (fun def_fwd->
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let anyclos = lower_anyclos_type ctxt at in
    let _, clos1 = lower_clos_type ctxt at arity [] in
    let argts, argv_opt = lower_param_types ctxt at arity in
    let _, curriedN = lower_clos_type ctxt at arity W.(ref_ anyclos :: argts) in
    emit_func ctxt at W.(ref_ anyclos :: argts) W.[eqref] (fun ctxt fn ->
      def_fwd fn;
      let ctxt = enter_scope ctxt LocalScope in
      let clos = emit_param ctxt at in
      let args = List.init (List.length argts) (fun _ -> emit_param ctxt at) in
      let arg0 = List.hd args in
(*
  if arity <= max_arity then begin
*)
      emit_block ctxt at W.block W.void (fun ctxt ->
        emit_block ctxt at W.block W.void (fun ctxt ->
          let rec over_apply ctxt = function
            | 0 ->
              (* Dispatch on closure arity *)
              let labs = List.init (arity + 1) (fun i -> int32 (max 0 (i - 1)) @@ at) in
              emit ctxt W.[
                local_get (clos @@ at);
                struct_get (anyclos @@ at) (clos_arity_idx @@ at);
                br_table labs (int32 arity @@ at);
              ]
            | n ->
              emit_block ctxt at W.block W.void (fun ctxt ->
                over_apply ctxt (n - 1);
              );
              (* Dispatching here when closure arity n < apply arity *)
              let codeN, closN = lower_func_type ctxt at n in
              (* Downcast closure type *)
              emit ctxt W.[
unreachable;
                local_get (clos @@ at);
                rtt_canon (anyclos @@ at);
                rtt_sub (closN @@ at);
                ref_cast;
              ];
              (* Bind result to local *)
              emit_let ctxt at W.void W.[ref_ closN] (fun ctxt ->
                (* Call target function with arguments it can handle *)
                emit ctxt W.[
                  local_get (0l @@ at);
                ];
                compile_load_args ctxt at 1l (arg0 +% 1l) 0 n argv_opt;
                emit ctxt W.[
                  local_get (0l @@ at);
                  struct_get (closN @@ at) (clos_code_idx @@ at);
                  call_ref;
                  (* Downcast resulting closure *)
                  ref_as_data;
                  rtt_canon (anyclos @@ at);
                  ref_cast;
                ];
                (* Apply result to remaining arguments *)
                compile_load_args ctxt at 1l (arg0 +% 1l) n arity argv_opt;
                emit ctxt W.[
                  call (compile_apply ctxt at (arity - n) @@ at);
                  return;  (* TODO: should be tail call *)
                ];
              )
          in over_apply ctxt (arity - 1)
        );
        (* Dispatching here when closure arity n = apply arity *)
        let codeN, closN = lower_func_type ctxt at arity in
        (* Downcast closure type *)
        emit ctxt W.[
          local_get (clos @@ at);
          rtt_canon (anyclos @@ at);
          rtt_sub (closN @@ at);
          ref_cast;
        ];
        (* Bind result to local *)
        emit_let ctxt at W.void W.[ref_ closN] (fun ctxt ->
          (* Call target function *)
          emit ctxt W.[
            local_get (0l @@ at);
          ];
          compile_load_args ctxt at 1l (arg0 +% 1l) 0 arity argv_opt;
          emit ctxt W.[
            local_get (0l @@ at);
            struct_get (closN @@ at) (clos_code_idx @@ at);
            call_ref;
            return;  (* TODO: should be tail call *)
          ]
        )
      );
      (* Dispatching here when closure arity > apply arity *)
      (* Create curried closure *)
      emit ctxt W.[
unreachable;
        i32_const (1l @@ at);
        ref_func (compile_curry ctxt at arity @@ at);
        local_get (clos @@ at);
      ];
      compile_load_args ctxt at 0l arg0 0 arity argv_opt;
      emit ctxt W.[
        rtt_canon (anyclos @@ at);
        rtt_sub (clos1 @@ at);
        rtt_sub (curriedN @@ at);
        struct_new (curriedN @@ at);
      ]
(*
  end else begin
    (* This code is agnostic to static arity, hence works for any *)
    let argv = Option.get argv_opt in
    let src_arity = emit_local ctxt at W.i32 in
    let dst_arity = emit_local ctxt at W.i32 in
    let _, closN = lower_func_type ctxt at n in
    emit ctxt W.[
      local_get (clos @@ at);
      rtt_canon (anyclos @@ at);
      rtt_sub (closN @@ at);
      ref_cast;
    ];
    emit_let ctxt at W.(result eqref) W.[ref_ closN] (fun ctxt ->
      emit_block ctxt at W.block W.void (fun ctxt ->
        emit_block ctxt at W.block W.void (fun ctxt ->
          emit ctxt W.[
            (* Load source arity *)
            local_get (arg0 +% 1l @@ at);
            array_len (argv @@ at);
            local_tee (src_arity +% 1l @@ at);
            (* Load destination arity *)
            local_get (0l @@ at);
            struct_get (anyclos @@ at) (close_arity_idx @@ at);
            local_tee (dst_arity +% 1l @@ at);
            (* Compare *)
            i32_lt_u;
            br_if (1l @@ at);
            local_get (src_arity +% 1l @@ at);
            local_get (dst_arity +% 1l @@ at);
            i32_gt_u;
            br_if (0l @@ at);
          ];
          (* Arities match, forward call *)
          emit ctxt W.[
            local_get (0l @@ at);
            local_get (arg0 +% 1l @@ at);  (* argv *)
            local_get (0l @@ at);
            struct_get (closN @@ at) (close_code_idx @@ at);
            call_ref;
            return;  (* TODO: should be tail call *)
          ]
        );
        (* Closure arity < call arity, split call *)
        emit ctxt W.[
          local_get (0l @@ at);
        ];
        compile_load_args ctxt at 1l (arg0 +% 1l) 0 n argv_opt;
        emit ctxt W.[
          call (compile_apply ctxt at (arity - n) @@ at);
        ];
        compile_load_args ctxt at 1l (arg0 +% 1l) n arity argv_opt;
        emit ctxt W.[
          call (compile_apply ctxt at (arity - n) @@ at);
          return;  (* TODO: should be tail call *)
        ];
      );
      (* Closure arity > call arity, curry *)
      emit ctxt W.[
        i32_const (1l @@ at);
        ref_func (compile_curry ctxt at arity @@ at);
        local_get (0l @@ at);
        local_get (arg0 +% 1l @@ at);
        rtt_canon (anyclos @@ at);
        rtt_sub (clos1 @@ at);
        rtt_sub (curriedN @@ at);
        struct_new (curriedN @@ at);
      ]
    )
  end
*)
    )
  )

and compile_curry ctxt at arity =
  let arity_string =
    if arity <= max_func_arity then string_of_int arity else "vec" in
  Emit.lookup_intrinsic ctxt ("curry" ^ arity_string) (fun def_fwd ->
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let anyclos = lower_anyclos_type ctxt at in
    let _, clos1 = lower_clos_type ctxt at arity [] in
    let argts, argv_opt = lower_param_types ctxt at arity in
    let codeN, curriedN =
      lower_clos_type ctxt at arity W.(ref_ anyclos :: argts) in
    (* curryN = fun xN => apply_N+1 x0 ... xN-1 xN *)
    emit_func ctxt at W.(ref_ clos1 :: argts) W.[eqref] (fun ctxt fn ->
      def_fwd fn;
      let ctxt = enter_scope ctxt LocalScope in
      let clos = emit_param ctxt at in
      let args = List.init (List.length argts) (fun _ -> emit_param ctxt at) in
      let arg0 = List.hd args in
      emit_func_ref ctxt at fn;
      (* Downcast generic to specific closure type *)
      emit ctxt W.[
        local_get (clos @@ at);
        rtt_canon (anyclos @@ at);
        rtt_sub (clos1 @@ at);
        rtt_sub (curriedN @@ at);
        ref_cast;
      ];
      (* Bind result to local *)
      emit_let ctxt at W.(result eqref) W.[ref_ curriedN] (fun ctxt ->
        (* Load arguments *)
        if arity <= max_func_arity then begin
          (* Load target function *)
          emit ctxt W.[
            local_get (0l @@ at);
            struct_get (curriedN @@ at) (curry_fun_idx @@ at);
          ];
          (* Target expects direct args, load them individually *)
          compile_args ctxt at 1l (arity + 1) (fun i ->
            if i < arity then
              (* First arity args are loaded from closure environment *)
              emit ctxt W.[
                local_get (0l @@ at);
                struct_get (curriedN @@ at) (curry_arg_idx +% int32 i @@ at);
              ]
            else
              (* Last arg is the applied one *)
              emit ctxt W.[
                local_get (arg0 +% 1l @@ at);
              ]
          );
          (* Call target *)
          emit ctxt W.[
            call (compile_apply ctxt at (arity + 1) @@ at);
            return;  (* TODO: should be tail call *)
          ]
        end else begin
          (* Target expects arg vector, copy to extended vector *)
          (* This code is agnostic to static arity, hence works for any *)
          let argv = Option.get argv_opt in
          let src = emit_local ctxt at W.(ref_null_ argv) in
          let dst = emit_local ctxt at W.(ref_null_ argv) in
          let len = emit_local ctxt at W.i32 in
          let i = emit_local ctxt at W.i32 in
          emit ctxt W.[
            (* Load source *)
            local_get (0l @@ at);  (* curriedN *)
            struct_get (curriedN @@ at) (curry_arg_idx @@ at);
            local_tee (src +% 1l @@ at);
            (* Load length *)
            array_len (argv @@ at);
            local_tee (i +% 1l @@ at);
            (* Allocate destination *)
            i32_const (1l @@ at);
            i32_add;
            local_tee (len +% 1l @@ at);
            rtt_canon (argv @@ at);
            array_new_default (argv @@ at);
            local_tee (dst +% 1l @@ at);
            (* Initialise applied argument *)
            local_get (i +% 1l @@ at);
            local_get (arg0 +% 1l @@ at);
            array_set (argv @@ at);
          ];
          (* Copy closure arguments, from upper to lower *)
          emit_block ctxt at W.block W.void (fun ctxt ->
            emit_block ctxt at W.loop W.void (fun ctxt ->
              emit ctxt W.[
                (* Check termination condition *)
                local_get (i +% 1l @@ at);
                i32_eqz;
                br_if (1l @@ at);
                (* Load destination *)
                local_get (dst +% 1l @@ at);
                (* Compute next index *)
                local_get (i +% 1l @@ at);
                i32_const (1l @@ at);
                i32_sub;
                local_tee (i +% 1l @@ at);
                (* Read arg value from source *)
                local_get (src +% 1l @@ at);
                local_get (i +% 1l @@ at);
                array_get (argv @@ at);
                (* Store arg value to destination *)
                array_set (argv @@ at);
                (* Iterate *)
                br (0l @@ at);
              ]
            )
          );
          emit_block ctxt at W.block W.void (fun ctxt ->
            let _, closNP = lower_clos_type ctxt at (arity + 1) [] in
            emit ctxt W.[
              (* Load source arity *)
              local_get (len +% 1l @@ at);
              (* Load destination arity *)
              local_get (0l @@ at);
              struct_get (curriedN @@ at) (curry_fun_idx @@ at);
              struct_get (anyclos @@ at) (clos_arity_idx @@ at);
              (* Compare *)
              i32_ne;
              br_if (0l @@ at);
              (* All arguments collected, perform call *)
              local_get (0l @@ at);
              struct_get (curriedN @@ at) (curry_fun_idx @@ at);
              rtt_canon (anyclos @@ at);
              rtt_sub (closNP @@ at);
              ref_cast;
            ];
            (* Bind closure at specific type *)
            emit_let ctxt at W.void W.[ref_ closNP] (fun ctxt ->
              emit ctxt W.[
                local_get (0l @@ at);
                local_get (dst +% 2l @@ at);
                ref_as_non_null;
                local_get (0l @@ at);
                struct_get (closNP @@ at) (clos_code_idx @@ at);
                call_ref;
                return;  (* TODO: should be tail call *)
              ]
            )
          );
          (* Still missing arguments, create new closure *)
          emit ctxt W.[
            i32_const (1l @@ at);
            ref_func (compile_curry ctxt at arity @@ at);
            local_get (0l @@ at);
            local_get (dst +% 1l @@ at);
            ref_as_non_null;
            rtt_canon (anyclos @@ at);
            rtt_sub (clos1 @@ at);
            rtt_sub (curriedN @@ at);
            struct_new (curriedN @@ at);
          ]
        end
      )
    )
  )


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


let rec find_var ctxt x envs : scope * (loc * func_loc option) =
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
  let scope, (loc, _) = find_var ctxt x ctxt.ext.envs in
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
      | LocalScope | ModuleScope -> DirectLoc (emit_local ctxt x.at t')
      | GlobalScope ->
        let const = default_const ctxt x.at (scope_rep scope) t in
        DirectLoc (emit_global ctxt x.at W.Mutable t' const)
    in
    env := E.extend_val !env x (loc, None)

  | VarP x when pass = RecPass ->
    let scope, env = current_scope ctxt in
    compile_coerce ctxt pat_rep (scope_rep scope) t x.at;
    (match scope, (E.find_val x !env).it with
    | PreScope, _ -> assert false
    | (LocalScope | ModuleScope), (DirectLoc idx, _) ->
      emit ctxt W.[local_set (idx @@ p.at)]
    | GlobalScope, (DirectLoc idx, _) ->
      emit ctxt W.[global_set (idx @@ p.at)]
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
    let _, (_, func_loc_opt) = find_var ctxt x ctxt.ext.envs in
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
      compile_path ctxt q (Source.et e) dst
    | T.Fun _ ->
      nyi e.at "partial constructor application"
    | _ ->
      assert false
    );
    None

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
        let ps = List.rev ps in
        let arity = List.length ps in
        let anyclos = lower_anyclos_type ctxt e.at in
        let _code, clos = lower_func_type ctxt e.at arity in
        let argts, argv_opt = lower_param_types ctxt e.at arity in
        let fn = emit_func ctxt e.at W.(ref_ clos :: argts) W.[eqref]
          (fun ctxt _ ->
            let ctxt = enter_scope ctxt LocalScope in
            let _clos = emit_param ctxt e2.at in
            let args = List.map (fun p -> emit_param ctxt p.at) ps in
            let arg0 = List.hd args in
            let partial = List.exists (fun p -> classify_pat p = PartialPat) ps in
            if not partial then
              List.iteri (fun i pI ->
                match classify_pat pI with
                | IrrelevantPat -> ()
                | TotalPat ->
                  compile_load_arg ctxt pI.at arg0 i argv_opt;
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
                      compile_load_arg ctxt pI.at arg0 i argv_opt;
                      compile_pat FullPass ctxt (-1l) pI;
                    | PartialPat ->
                      compile_load_arg ctxt pI.at arg0 i argv_opt;
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
          rtt_canon (anyclos @@ e.at);
          rtt_sub (clos @@ e.at);
          struct_new (clos @@ e.at);
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
          nyi e.at "partial constructor application"

        | _ ->
          assert false
        )

      | _ ->
        (match compile_exp_func_opt ctxt UnboxedRigidRep e1 with
        | Some {funcidx; arity} when arity = List.length es ->
          let anyclos = lower_anyclos_type ctxt e1.at in
          let _, closN = lower_clos_type ctxt e1.at arity [] in
          emit ctxt W.[
            rtt_canon (anyclos @@ e1.at);
            rtt_sub (closN @@ e1.at);
            ref_cast;
          ];
          compile_args ctxt e.at 0l (List.length es) (fun i ->
            compile_exp ctxt BoxedRep (List.nth es i)
          );
          emit ctxt W.[
            call (funcidx @@ e.at);
          ]
        | _ ->
          compile_args ctxt e.at 0l (List.length es) (fun i ->
            compile_exp ctxt BoxedRep (List.nth es i)
          );
          emit ctxt W.[
            call (compile_apply ctxt e.at (List.length es) @@ e.at);
          ]
        );
        compile_coerce ctxt BoxedRep dst (Source.et e) e.at
    in flat e1 [e2];
    None
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
