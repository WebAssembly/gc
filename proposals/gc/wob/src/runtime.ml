let module_name = "wob-runtime"
let _name_text_new = "text_new"
let _name_text_cpy = "text_cpy"
let name_text_cat = "text_cat"
let name_text_eq = "text_eq"
let name_rtt_eq = "rtt_eq"


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
  [ (* text_new needs access to local memory, can't be shared in runtime. *)
    (* name_text_new, (compile_text_new, ty [i32; i32] [text]); *)
    (* name_text_cpy, (compile_text_cpy, ty [text; i32; text; i32; i32] []); *)
    name_text_cat, (compile_text_cat, ty [text; text] [text]);
    name_text_eq, (compile_text_eq, ty [text; text] [i32]);
    name_rtt_eq, (compile_rtt_eq, ty [rtt; rtt] [i32]);
  ]

let compile_runtime () : Wasm.Ast.module_ =
  let ctxt = Emit.make_ctxt () in
  List.iter (fun (export, (compile, _)) ->
    Emit.emit_func_export ctxt Prelude.region export (compile ctxt)
  ) funcs;
  Emit.gen_module ctxt Prelude.region


let compile_runtime_import ctxt =
  let ctxt' = {ctxt with Emit.ext = ()} in  (* ensure polymorphism *)
  List.iteri (fun i (name, (compile, _)) ->
    let _, emit_type = List.assoc name funcs in
    let idx =
      Emit.emit_func_import ctxt' Prelude.region module_name name (emit_type ctxt')
    in assert (Int32.to_int idx = i)
  ) funcs

let import name ctxt =
  assert (not !Flags.headless);
  Option.get (Wasm.Lib.List32.index_where (fun (name', _) -> name = name') funcs)

(*let import_text_new ctxt = import name_text_new ctxt*)
(*let import_text_cpy ctxt = import name_text_cpy ctxt*)
let import_text_cat ctxt = import name_text_cat ctxt
let import_text_eq ctxt = import name_text_eq ctxt
let import_rtt_eq ctxt = import name_rtt_eq ctxt
