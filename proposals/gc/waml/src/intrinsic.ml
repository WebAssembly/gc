open Emit

let (@@) = W.Source.(@@)


(* Intrinsics *)

let lower_text_type ctxt : int32 =
  emit_type ctxt Prelude.region W.(type_array (field_mut_pack i8))


let compile_text_new ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_new" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_null_ text) in
    emit_func ctxt at W.[i32; i32] [textref] (fun ctxt _ ->
      let src = emit_param ctxt at in
      let len = emit_param ctxt at in
      let dst = emit_local ctxt at textref in
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
      ]
    )
  )

let compile_text_cpy ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_cpy" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_null_ text) in
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
    let textref = W.(ref_null_ text) in
    emit_func ctxt at [textref; textref] [textref] (fun ctxt _ ->
      let arg1 = emit_param ctxt at in
      let arg2 = emit_param ctxt at in
      let tmp = emit_local ctxt at textref in
      List.iter (emit_instr ctxt at) W.[
        local_get (arg1 @@ at);
        array_len (text @@ at);
        local_get (arg2 @@ at);
        array_len (text @@ at);
        i32_add;
        rtt_canon (text @@ at);
        array_new_default (text @@ at);
        local_tee (tmp @@ at);
        i32_const (0l @@ at);
        local_get (arg1 @@ at);
        i32_const (0l @@ at);
        local_get (arg1 @@ at);
        array_len (text @@ at);
        call (text_cpy @@ at);
        local_get (tmp @@ at);
        local_get (arg1 @@ at);
        array_len (text @@ at);
        local_get (arg2 @@ at);
        i32_const (0l @@ at);
        local_get (arg2 @@ at);
        array_len (text @@ at);
        call (text_cpy @@ at);
        local_get (tmp @@ at);
      ]
    )
  )

let compile_text_eq ctxt : int32 =
  Emit.lookup_intrinsic ctxt "text_eq" (fun _ ->
    let at = Prelude.region in
    let text = lower_text_type ctxt in
    let textref = W.(ref_null_ text) in
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
          array_len (text @@ at);
          local_get (arg2 @@ at);
          array_len (text @@ at);
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
              i32_eq;
              br_if (0l @@ at);
            ])
          ]);
          i32_const (1l @@ at);
          return;
        ]);
        i32_const (0l @@ at);
      ]
    )
  )
