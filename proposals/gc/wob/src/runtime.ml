let module_name = "wob-runtime"
let name_text_new = "text_new"
let _name_text_cpy = "text_cpy"
let name_text_cat = "text_cat"
let name_text_eq = "text_eq"
let name_rtt_eq = "rtt_eq"
let name_mem_alloc = "mem_alloc"
let name_mem = "mem"


let funcs =
  let open Intrinsic in
  let open Wasm.Types in
  let text ctxt = RefType (Nullable, DefHeapType (SynVar (compile_text_type ctxt))) in
  let rtt ctxt = RefType (Nullable, EqHeapType) in
  let i32 ctxt = NumType I32Type in
  let ty fts1 fts2 ctxt =
    let with_ctxt f = f ctxt in
    FuncType (List.map with_ctxt fts1, List.map with_ctxt fts2)
  in
  [ name_mem_alloc, (compile_mem_alloc, ty [i32] [i32]);
    name_text_new, (compile_text_new, ty [i32; i32] [text]);
    (* name_text_cpy, (compile_text_cpy, ty [text; i32; text; i32; i32] []); *)
    name_text_cat, (compile_text_cat, ty [text; text] [text]);
    name_text_eq, (compile_text_eq, ty [text; text] [i32]);
  ] @
  (if !Flags.parametric then [] else [
    name_rtt_eq, (compile_rtt_eq, ty [rtt; rtt] [i32]);
  ])


let compile_runtime () : Wasm.Ast.module_ =
  let ctxt = Emit.make_ctxt () in
  Emit.emit_memory_export ctxt Prelude.region name_mem
    (Intrinsic.compile_mem ctxt);
  List.iter (fun (export, (compile, _)) ->
    Emit.emit_func_export ctxt Prelude.region export (compile ctxt)
  ) funcs;
  Emit.gen_module ctxt Prelude.region


let import_func name ctxt =
  assert (not !Flags.headless);
  Emit.lookup_intrinsic ctxt name (fun _ ->
    let ctxt' = {ctxt with Emit.ext = ()} in  (* ensure polymorphism *)
    let _, emit_type = List.assoc name funcs in
    Emit.emit_func_import ctxt' Prelude.region module_name name (emit_type ctxt')
  )

let import_mem_alloc ctxt =
  Emit.lookup_intrinsic ctxt name_mem (fun _ ->
    Emit.emit_memory_import ctxt Prelude.region module_name name_mem 0l None
  ) |> ignore;
  import_func name_mem_alloc ctxt
let import_text_new ctxt = import_func name_text_new ctxt
(*let import_text_cpy ctxt = import_func name_text_cpy ctxt*)
let import_text_cat ctxt = import_func name_text_cat ctxt
let import_text_eq ctxt = import_func name_text_eq ctxt
let import_rtt_eq ctxt = import_func name_rtt_eq ctxt
