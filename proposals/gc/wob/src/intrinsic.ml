open Emit

let (@@) = W.Source.(@@)


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

let compile_text_type ctxt : int32 =
  let ft = W.(FieldType (PackedStorageType Pack8, Mutable)) in
  emit_type ctxt Prelude.region W.(sub [] (array ft))


let compile_text_new ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_new" (fun _ ->
    let at = Prelude.region in
    let typeidx = compile_text_type ctxt in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at W.[i32; i32] [t'] (fun ctxt _ ->
      let srcidx = emit_param ctxt at in
      let lenidx = emit_param ctxt at in
      let dstidx = emit_local ctxt at t' in
      List.iter (emit_instr ctxt at) W.[
        local_get (lenidx @@ at);
        rtt_canon (typeidx @@ at);
        array_new_default (typeidx @@ at);
        local_set (dstidx @@ at);
        block void (List.map (fun e -> e @@ at) [
          loop void (List.map (fun e -> e @@ at) [
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
  )

let compile_text_cpy ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_cpy" (fun _ ->
    let at = Prelude.region in
    let typeidx = compile_text_type ctxt in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at W.[t'; i32; t'; i32; i32] [] (fun ctxt _ ->
      let dstidx = emit_param ctxt at in
      let dstkidx = emit_param ctxt at in
      let srcidx = emit_param ctxt at in
      let srckidx = emit_param ctxt at in
      let lenidx = emit_param ctxt at in
      emit_instr ctxt at W.(
        block void (List.map (fun e -> e @@ at) [
          loop void (List.map (fun e -> e @@ at) [
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
  )

let compile_text_cat ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_cat" (fun _ ->
    let text_cpy = compile_text_cpy ctxt in
    let at = Prelude.region in
    let typeidx = compile_text_type ctxt in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at [t'; t'] [t'] (fun ctxt _ ->
      let arg1idx = emit_param ctxt at in
      let arg2idx = emit_param ctxt at in
      let tmpidx = emit_local ctxt at t' in
      List.iter (emit_instr ctxt at) W.[
        local_get (arg1idx @@ at);
        array_len;
        local_get (arg2idx @@ at);
        array_len;
        i32_add;
        rtt_canon (typeidx @@ at);
        array_new_default (typeidx @@ at);
        local_tee (tmpidx @@ at);
        i32_const (0l @@ at);
        local_get (arg1idx @@ at);
        i32_const (0l @@ at);
        local_get (arg1idx @@ at);
        array_len;
        call (text_cpy @@ at);
        local_get (tmpidx @@ at);
        local_get (arg1idx @@ at);
        array_len;
        local_get (arg2idx @@ at);
        i32_const (0l @@ at);
        local_get (arg2idx @@ at);
        array_len;
        call (text_cpy @@ at);
        local_get (tmpidx @@ at);
      ]
    )
  )

let compile_text_eq ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_eq" (fun _ ->
    let at = Prelude.region in
    let typeidx = compile_text_type ctxt in
    let t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    emit_func ctxt at [t'; t'] W.[i32] (fun ctxt _ ->
      let arg1idx = emit_param ctxt at in
      let arg2idx = emit_param ctxt at in
      let lenidx = emit_local ctxt at W.i32 in
      List.iter (emit_instr ctxt at) W.[
        block void (List.map (fun e -> e @@ at) [
          local_get (arg1idx @@ at);
          local_get (arg2idx @@ at);
          ref_eq;
          if_ void (List.map (fun e -> e @@ at) [
            i32_const (1l @@ at); return
          ]) [];
          local_get (arg1idx @@ at);
          array_len;
          local_get (arg2idx @@ at);
          array_len;
          local_tee (lenidx @@ at);
          i32_ne;
          br_if (0l @@ at);
          block void (List.map (fun e -> e @@ at) [
            loop void (List.map (fun e -> e @@ at) [
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


(* Runtime types *)

let compile_rtt_type ctxt : int32 =
  let rtt_vt = W.(RefType (Nullable, EqHeapType)) in
  let rtt_ft = W.(FieldType (ValueStorageType rtt_vt, Mutable)) in
  emit_type ctxt Prelude.region W.(sub [] (array rtt_ft))

let compile_rtt_eq ctxt : int32 =
  Emit.lookup_intrinsic ctxt "rtt_eq" (fun _ ->
    let at = Prelude.region in
    let typeidx = compile_rtt_type ctxt in
    let rtt_t' = W.(RefType (Nullable, DefHeapType (SynVar typeidx))) in
    let t' = W.(RefType (Nullable, EqHeapType)) in
    emit_func ctxt at [t'; t'] W.[i32] (fun ctxt selfidx ->
      let arg1idx = emit_param ctxt at in
      let arg2idx = emit_param ctxt at in
      let rtt1idx = emit_local ctxt at rtt_t' in
      let rtt2idx = emit_local ctxt at rtt_t' in
      let lenidx = emit_local ctxt at W.i32 in
      List.iter (emit_instr ctxt at) W.[
        block void (List.map (fun e -> e @@ at) [
          local_get (arg1idx @@ at);
          local_get (arg2idx @@ at);
          ref_eq;
          if_ void (List.map (fun e -> e @@ at) [
            i32_const (1l @@ at);
            return;
          ]) [];
          block void (List.map (fun e -> e @@ at) [
            block (result t') (List.map (fun e -> e @@ at) [
              local_get (arg1idx @@ at);
              br_on_non_data (0l @@ at);
              rtt_canon (typeidx @@ at);
              br_on_cast_fail (0l @@ at);
              local_set (rtt1idx @@ at);
              local_get (arg2idx @@ at);
              br_on_non_data (0l @@ at);
              rtt_canon (typeidx @@ at);
              br_on_cast_fail (0l @@ at);
              local_set (rtt2idx @@ at);
              br (1l @@ at);
            ]);
            drop;
            i32_const (0l @@ at);
            return;
          ]);
          local_get (rtt1idx @@ at);
          array_len;
          local_set (lenidx @@ at);
          block void (List.map (fun e -> e @@ at) [
            loop void (List.map (fun e -> e @@ at) [
              local_get (lenidx @@ at);
              i32_eqz;
              br_if (1l @@ at);
              local_get (rtt1idx @@ at);
              local_get (lenidx @@ at);
              i32_const (1l @@ at);
              i32_sub;
              local_tee (lenidx @@ at);
              array_get (typeidx @@ at);
              local_get (rtt2idx @@ at);
              local_get (lenidx @@ at);
              array_get (typeidx @@ at);
              call (selfidx @@ at);
              i32_eqz;
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
