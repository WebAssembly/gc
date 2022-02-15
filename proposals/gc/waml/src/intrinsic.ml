open Emit
open Lower

type ctxt = Lower.ctxt

let (@@) = W.Source.(@@)
let (+%) = Int32.add
let int32 = W.I32.of_int_s


(* Memory *)

let compile_mem ctxt : int32 =
  Emit.lookup_intrinsic ctxt "mem" (fun _ ->
    let at = Prelude.region in
    emit_memory ctxt at 1l None
  )

let compile_mem_ptr ctxt : int32 =
  Emit.lookup_intrinsic ctxt "mem_ptr" (fun _ ->
    let at = Prelude.region in
    emit_global ctxt at W.Mutable W.i32 None
  )

let compile_mem_alloc ctxt : int32 =
  Emit.lookup_intrinsic ctxt "mem_alloc" (fun _ ->
    let at = Prelude.region in
    emit_func ctxt at W.[i32] W.[i32] (fun ctxt _ ->
      let argidx = emit_param ctxt at in
      let addridx = emit_local ctxt at W.i32 in
      let deltaidx = emit_local ctxt at W.i32 in
      let freeidx = compile_mem_ptr ctxt in
      let _ = compile_mem ctxt in
      List.iter (emit_instr ctxt at) W.[
        global_get (freeidx @@ at);
        local_tee (addridx @@ at);
        local_get (argidx @@ at);
        i32_add;
        global_set (freeidx @@ at);
        block void (List.map (fun e -> e @@ at) [
          global_get (freeidx @@ at);
          i32_const (0xffffl @@ at);
          i32_add;
          i32_const (16l @@ at);
          i32_shr_u;
          memory_size;
          i32_sub;
          local_tee (deltaidx @@ at);
          i32_eqz;
          br_if (0l @@ at);
          local_get (deltaidx @@ at);
          memory_grow;
          i32_const (-1l @@ at);
          i32_ne;
          br_if (0l @@ at);
          unreachable;
        ]);
        local_get (addridx @@ at);
      ]
    )
  )


(* Text *)

let lower_text_type ctxt : int32 =
  emit_type ctxt Prelude.region W.(sub [] (array (field_mut_pack i8)))


let compile_text_new ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_new" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_ text) in
    let textnullref = W.(ref_null_ text) in
    emit_func ctxt at W.[i32; i32] [textref] (fun ctxt _ ->
      let src = emit_param ctxt at in
      let len = emit_param ctxt at in
      let dst = emit_local ctxt at textnullref in
      List.iter (emit_instr ctxt at) W.[
        local_get (len @@ at);
        rtt_canon (text @@ at);
        array_new_default (text @@ at);
        local_set (dst @@ at);
        block void (List.map (fun e -> e @@ at) [
          loop void (List.map (fun e -> e @@ at) [
            local_get (len @@ at);
            i32_eqz;
            br_if (1l @@ at);
            local_get (dst @@ at);
            local_get (len @@ at);
            i32_const (1l @@ at);
            i32_sub;
            local_tee (len @@ at);
            local_get (len @@ at);
            local_get (src @@ at);
            i32_add;
            i32_load8_u 0 0l;
            array_set (text @@ at);
            br (0l @@ at);
          ])
        ]);
        local_get (dst @@ at);
        ref_as_non_null;
      ]
    )
  )

let compile_text_cpy ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_cpy" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_ text) in
    emit_func ctxt at W.[textref; i32; textref; i32; i32] [] (fun ctxt _ ->
      let dst = emit_param ctxt at in
      let dstk = emit_param ctxt at in
      let src = emit_param ctxt at in
      let srck = emit_param ctxt at in
      let len = emit_param ctxt at in
      emit_instr ctxt at W.(
        block void (List.map (fun e -> e @@ at) [
          loop void (List.map (fun e -> e @@ at) [
            local_get (len @@ at);
            i32_eqz;
            br_if (1l @@ at);
            local_get (dst @@ at);
            local_get (len @@ at);
            i32_const (1l @@ at);
            i32_sub;
            local_tee (len @@ at);
            local_get (dstk @@ at);
            i32_add;
            local_get (src @@ at);
            local_get (len @@ at);
            local_get (srck @@ at);
            i32_add;
            array_get_u (text @@ at);
            array_set (text @@ at);
            br (0l @@ at);
          ])
        ])
      )
    )
  )

let compile_text_cat ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_cat" (fun _ ->
    let text_cpy = compile_text_cpy ctxt in
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_ text) in
    let textnullref = W.(ref_null_ text) in
    emit_func ctxt at [textref; textref] [textref] (fun ctxt _ ->
      let arg1 = emit_param ctxt at in
      let arg2 = emit_param ctxt at in
      let tmp = emit_local ctxt at textnullref in
      List.iter (emit_instr ctxt at) W.[
        local_get (arg1 @@ at);
        array_len;
        local_get (arg2 @@ at);
        array_len;
        i32_add;
        rtt_canon (text @@ at);
        array_new_default (text @@ at);
        local_tee (tmp @@ at);
        ref_as_non_null;
        i32_const (0l @@ at);
        local_get (arg1 @@ at);
        i32_const (0l @@ at);
        local_get (arg1 @@ at);
        array_len;
        call (text_cpy @@ at);
        local_get (tmp @@ at);
        ref_as_non_null;
        local_get (arg1 @@ at);
        array_len;
        local_get (arg2 @@ at);
        i32_const (0l @@ at);
        local_get (arg2 @@ at);
        array_len;
        call (text_cpy @@ at);
        local_get (tmp @@ at);
        ref_as_non_null;
      ]
    )
  )

let compile_text_eq ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_eq" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_ text) in
    emit_func ctxt at [textref; textref] W.[i32] (fun ctxt _ ->
      let arg1 = emit_param ctxt at in
      let arg2 = emit_param ctxt at in
      let len = emit_local ctxt at W.i32 in
      List.iter (emit_instr ctxt at) W.[
        block void (List.map (fun e -> e @@ at) [
          local_get (arg1 @@ at);
          local_get (arg2 @@ at);
          ref_eq;
          if_ void (List.map (fun e -> e @@ at) [
            i32_const (1l @@ at); return
          ]) [];
          local_get (arg1 @@ at);
          array_len;
          local_get (arg2 @@ at);
          array_len;
          local_tee (len @@ at);
          i32_ne;
          br_if (0l @@ at);
          block void (List.map (fun e -> e @@ at) [
            loop void (List.map (fun e -> e @@ at) [
              local_get (len @@ at);
              i32_eqz;
              br_if (1l @@ at);
              local_get (arg1 @@ at);
              local_get (len @@ at);
              i32_const (1l @@ at);
              i32_sub;
              local_tee (len @@ at);
              array_get_u (text @@ at);
              local_get (arg2 @@ at);
              local_get (len @@ at);
              array_get_u (text @@ at);
              i32_ne;
              br_if (2l @@ at);
              br (0l @@ at);
            ])
          ]);
          i32_const (1l @@ at);
          return;
        ]);
        i32_const (0l @@ at);
      ]
    )
  )


(* Application and combinators *)

let curry_fun_idx = clos_env_idx
let curry_arg_idx = clos_env_idx +% 1l  (* first argument or argv *)

let compile_push_args ctxt at n shift compile_eI =
  let emit ctxt = List.iter (emit_instr ctxt at) in
  match lower_param_types ctxt at n with
  | _, None ->
    for i = 0 to n - 1 do
      compile_eI i
    done
  | _, Some argv ->
    let tmp = emit_local ctxt at W.(ref_null_ argv) in
    emit ctxt W.[
      i32_const (0l @@ at);
      i31_new;
      i32_const (int32 n @@ at);
      rtt_canon (argv @@ at);
      array_new (argv @@ at);
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

let compile_load_arg ctxt at i arg0 argv_opt =
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
      ref_as_non_null;
    ]

let compile_load_args ctxt at i j shift arg0 src_argv_opt =
  assert (j <= max_func_arity || src_argv_opt <> None);
  if j - i > max_func_arity && i = 0 then
    (* Reuse argv *)
    emit_instr ctxt at W.(local_get (arg0 +% shift @@ at))
  else
    compile_push_args ctxt at (j - i) shift (fun k ->
      compile_load_arg ctxt at (i + k) (arg0 +% shift) src_argv_opt
    )

let rec compile_func_apply arity ctxt =
  assert (arity > 0);
  Emit.lookup_intrinsic ctxt ("func_apply" ^ string_of_int arity) (fun def_fwd ->
    let at = Prelude.region in
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let anyclos = lower_anyclos_type ctxt at in
    let argts, argv_opt = lower_param_types ctxt at arity in
    emit_func ctxt at W.(ref_ anyclos :: argts) [absref] (fun ctxt fn ->
      def_fwd fn;
      let clos = emit_param ctxt at in
      let args = List.map (fun _ -> emit_param ctxt at) argts in
      let arg0 = List.hd args in
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
              let _, closN = lower_func_type ctxt at n in
              (* Downcast closure type *)
              emit ctxt W.[
                local_get (clos @@ at);
                rtt_canon (closN @@ at);
                ref_cast;
              ];
              (* Bind result to local *)
              emit_let ctxt at W.void W.[ref_ closN] (fun ctxt ->
                (* Call target function with arguments it can handle *)
                emit ctxt W.[
                  local_get (0l @@ at);
                ];
                compile_load_args ctxt at 0 n 1l arg0 argv_opt;
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
                compile_load_args ctxt at n arity 1l arg0 argv_opt;
                emit ctxt W.[
                  call (compile_func_apply (arity - n) ctxt @@ at);
                  return;  (* TODO: should be tail call *)
                ];
              )
          in over_apply ctxt (arity - 1)
        );
        (* Dispatching here when closure arity n = apply arity *)
        let _, closN = lower_func_type ctxt at arity in
        (* Downcast closure type *)
        emit ctxt W.[
          local_get (clos @@ at);
          rtt_canon (closN @@ at);
          ref_cast;
        ];
        (* Bind result to local *)
        emit_let ctxt at W.void W.[ref_ closN] (fun ctxt ->
          (* Call target function *)
          emit ctxt W.[
            local_get (0l @@ at);
          ];
          compile_load_args ctxt at 0 arity 1l arg0 argv_opt;
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
      let flds = List.map W.field W.(ref_ anyclos :: argts) in
      let _, clos1, curriedN = lower_clos_type ctxt at 1 flds in
      emit ctxt W.[
        i32_const (1l @@ at);
        ref_func (compile_func_curry arity ctxt @@ at);
        local_get (clos @@ at);
      ];
      compile_load_args ctxt at 0 arity 0l arg0 argv_opt;
      emit ctxt W.[
        rtt_canon (curriedN @@ at);
        struct_new (curriedN @@ at);
      ]
    )
  )

and compile_func_curry arity ctxt =
  let arity_string =
    if arity <= max_func_arity then string_of_int arity else "vec" in
  Emit.lookup_intrinsic ctxt ("func_curry" ^ arity_string) (fun def_fwd ->
    let at = Prelude.region in
    let emit ctxt = List.iter (emit_instr ctxt at) in
    let anyclos = lower_anyclos_type ctxt at in
    let argts, argv_opt = lower_param_types ctxt at arity in
    let flds = List.map W.field W.(ref_ anyclos :: argts) in
    let _, clos1, curriedN = lower_clos_type ctxt at 1 flds in
    (* curryN = fun xN => apply_N+1 x0 ... xN-1 xN *)
    emit_func ctxt at W.[ref_ clos1; absref] [absref] (fun ctxt fn ->
      def_fwd fn;
      let clos = emit_param ctxt at in
      let arg0 = emit_param ctxt at in
      emit_func_ref ctxt at fn;
      (* Downcast generic to specific closure type *)
      emit ctxt W.[
        local_get (clos @@ at);
        rtt_canon (curriedN @@ at);
        ref_cast;
      ];
      (* Bind result to local *)
      emit_let ctxt at W.(result absref) W.[ref_ curriedN] (fun ctxt ->
        (* Load arguments *)
        if arity <= max_func_arity then begin
          (* Load target function *)
          emit ctxt W.[
            local_get (0l @@ at);
            struct_get (curriedN @@ at) (curry_fun_idx @@ at);
          ];
          (* Target expects direct args, load them individually *)
          compile_push_args ctxt at (arity + 1) 1l (fun i ->
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
            call (compile_func_apply (arity + 1) ctxt @@ at);
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
            (* Array init value *)
            i32_const (0l @@ at);
            i31_new;
            (* Load source *)
            local_get (0l @@ at);  (* curriedN *)
            struct_get (curriedN @@ at) (curry_arg_idx @@ at);
            local_tee (src +% 1l @@ at);
            (* Load length *)
            array_len;
            local_tee (i +% 1l @@ at);
            (* Allocate destination *)
            i32_const (1l @@ at);
            i32_add;
            local_tee (len +% 1l @@ at);
            rtt_canon (argv @@ at);
            array_new (argv @@ at);
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
            let _, closNP = lower_func_type ctxt at (arity + 1) in
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
              rtt_canon (closNP @@ at);
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
            ref_func (compile_func_curry arity ctxt @@ at);
            local_get (0l @@ at);
            struct_get (curriedN @@ at) (curry_fun_idx @@ at);
            local_get (dst +% 1l @@ at);
            ref_as_non_null;
            rtt_canon (curriedN @@ at);
            struct_new (curriedN @@ at);
          ]
        end
      )
    )
  )
