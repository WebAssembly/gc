open Wasm.Source
open Wasm.Ast
open Wasm.Types


(* Errors & Tracing *)

exception Mismatch of string * string

let error file msg = raise (Mismatch (file, msg))

let trace name = if !Flags.trace then print_endline ("-- " ^ name)


(* Environment *)

module Map = Map.Make(String)

type counts =
  { ntypes : int32;
    nfuncs : int32;
    nglobals : int32;
    ntables : int32;
    nmemories : int32;
    nelems : int32;
    ndatas : int32;
  }

type env =
  { imports : counts;  (* import bindings so far *)
    binds : counts;  (* total bindings so far *)
    exports : (export * extern_type) list Map.t;  (* exports for all modules *)
    subst : Subst.t;  (* substitution for current module *)
  }

let (+%) = Int32.add
let inc_func cnt = {cnt with nfuncs = cnt.nfuncs +% 1l}
let inc_global cnt = {cnt with nglobals = cnt.nglobals +% 1l}
let inc_table cnt = {cnt with ntables = cnt.ntables +% 1l}
let inc_memory cnt = {cnt with nmemories = cnt.nmemories +% 1l}

let empty_cnt =
  { ntypes = 0l;
    nfuncs = 0l;
    nglobals = 0l;
    ntables = 0l;
    nmemories = 0l;
    nelems = 0l;
    ndatas = 0l;
  }

let empty_env =
  { imports = empty_cnt;
    binds = empty_cnt;
    exports = Map.empty;
    subst = Subst.empty
  }


(* Precompute binding offsets due to remaining imports *)

let inc_for idesc =
  match idesc.it with
  | FuncImport _ -> inc_func
  | GlobalImport _ -> inc_global
  | TableImport _ -> inc_table
  | MemoryImport _ -> inc_memory

let rec resolve_imports (env : env) ims : env =
  match ims with
  | [] -> env
  | im::ims' ->
    let mname = Wasm.Utf8.encode im.it.module_name in
    if Map.find_opt mname env.exports = None then
      resolve_imports {env with binds = inc_for im.it.idesc env.binds} ims'
    else
      resolve_imports env ims'

let dummy_et = ExternFuncT (DefT (RecT [], -1l))
let resolve_exports (env : env) file exs : env =
  let name = Filename.chop_extension file in
  let ets = List.map (fun _ -> dummy_et) exs in
  {env with exports = Map.add name (List.combine exs ets) env.exports}

let rec resolve_modules (env : env) (modules : (string * module_) list) mems
  : env * string list =
  match modules with
  | [] -> env, List.rev mems
  | (file, m)::modules' ->
    let env' = resolve_imports env m.it.imports in
    let env'' = resolve_exports env' file m.it.exports in
    resolve_modules env'' modules' (if m.it.memories = [] then mems else file::mems)


(* Merging *)

let rec merge_imports (env : env) file m ts ims cnt ims_out : env * counts * import list =
  match ims with
  | [] -> env, cnt, List.rev ims_out
  | im::ims' ->
    let {module_name; item_name; idesc} = im.it in
    let mname = Wasm.Utf8.encode module_name in
    let iname = Wasm.Utf8.encode item_name in
    match Map.find_opt mname env.exports with
    | None ->
      let subst' =
        match idesc.it with
        | FuncImport _ ->
          Subst.add_func env.subst cnt.nfuncs env.imports.nfuncs
        | GlobalImport _ ->
          Subst.add_global env.subst cnt.nglobals env.imports.nglobals
        | TableImport _ ->
          Subst.add_table env.subst cnt.ntables env.imports.ntables
        | MemoryImport _ ->
          Subst.add_memory env.subst cnt.nmemories env.imports.nmemories
      in
      let env' = {env with subst = subst'; imports = inc_for idesc env.imports} in
      merge_imports env' file m ts ims' (inc_for idesc cnt) (im::ims_out)
    | Some exs ->
      match List.find_opt (fun (ex, _) -> ex.it.name = item_name) exs with
      | None ->
        error file (
          "imported module \"" ^ mname ^ "\" " ^
          "does not export item \"" ^ iname ^ "\""
        )
      | Some (ex, et) ->
        if not !Flags.unchecked then begin
          let it = extern_type_of_import_type (import_type_of m im) in
          if not (Wasm.Match.match_extern_type ts et it) then
            error file (
              "imported module \"" ^ mname ^ "\" " ^
              "exports item \"" ^ iname ^ "\" with incompatible type\n" ^
              "export type: " ^ string_of_extern_type et ^ "\n" ^
              "import type: " ^ string_of_extern_type it
            )
        end;
        let subst' =
          match idesc.it, ex.it.edesc.it with
          | FuncImport _, FuncExport y ->
            Subst.add_func env.subst cnt.nfuncs y.it
          | GlobalImport _, GlobalExport y ->
            Subst.add_global env.subst cnt.nglobals y.it
          | TableImport _, TableExport y ->
            Subst.add_table env.subst cnt.ntables y.it
          | MemoryImport _, MemoryExport y ->
            Subst.add_memory env.subst cnt.nmemories y.it
          | _, _ ->
            error file (
              "imported module \"" ^ mname ^ "\" " ^
              "exports item \"" ^ iname ^ "\" with incompatible kind"
            )
        in merge_imports {env with subst = subst'} file m ts ims' (inc_for idesc cnt) ims_out

let rec add_range s x y = function
  | [] -> s
  | _::defs -> add_range (Subst.Map.add x y s) (x +% 1l) (y +% 1l) defs

let rec add_types_range s x y = function
  | [] -> s
  | {it = RecT []; at}::dts ->
    add_types_range s x y dts
  | {it = RecT (st::sts); at}::dts ->
    add_types_range (Subst.Map.add x y s) (x +% 1l) (y +% 1l)
      ({it = RecT sts; at}::dts)

let rec num_types = function
  | [] -> 0l
  | {it = RecT sts; _}::dts -> Wasm.Lib.List32.length sts +% num_types dts

let merge_defs (env : env) cnt m : env =
  let open Subst in
  let {subst; binds; _} = env in
  let subst' =
    { stype = add_types_range subst.stype 0l binds.ntypes m.it.types;
      sfunc = add_range subst.sfunc cnt.nfuncs binds.nfuncs m.it.funcs;
      sglobal = add_range subst.sglobal cnt.nglobals binds.nglobals m.it.globals;
      stable = add_range subst.stable cnt.ntables binds.ntables m.it.tables;
      smemory = add_range subst.smemory cnt.nmemories binds.nmemories m.it.memories;
      selem = add_range subst.selem 0l binds.nelems m.it.elems;
      sdata = add_range subst.sdata 0l binds.ndatas m.it.datas;
      slocal = Map.empty;
      slabel = Map.empty;
    }
  in
  let binds' =
    { ntypes = binds.ntypes +% num_types m.it.types;
      nfuncs = binds.nfuncs +% Wasm.Lib.List32.length m.it.funcs;
      nglobals = binds.nglobals +% Wasm.Lib.List32.length m.it.globals;
      ntables = binds.ntables +% Wasm.Lib.List32.length m.it.tables;
      nmemories = binds.nmemories +% Wasm.Lib.List32.length m.it.memories;
      nelems = binds.nelems +% Wasm.Lib.List32.length m.it.elems;
      ndatas = binds.ndatas +% Wasm.Lib.List32.length m.it.datas;
    }
  in
  {env with subst = subst'; binds = binds'}

let merge_exports (env : env) file m ts exs : env =
  let name = Filename.chop_extension file in
  let ets =
    if !Flags.unchecked
    then List.map (fun _ -> dummy_et) exs
    else List.map (fun ex ->
      extern_type_of_export_type (export_type_of m ex)) m.it.exports
  in
  {env with exports = Map.add name (List.combine exs ets) env.exports}

let merge_start (env : env) starts m : module_' =
  match starts with
  | [] -> m
  | [st] -> {m with start = Some st}
  | st0::_ ->
    let ftype = (Wasm.Lib.List32.nth m.funcs st0.it.sfunc.it).it.ftype in
    let body = List.map (fun st -> Call st.it.sfunc @@ no_region) starts in
    let f = {ftype; locals = []; body} @@ no_region in
    let start = {sfunc = env.binds.nfuncs @@ no_region} @@ no_region in
    {m with start = Some start; funcs = m.funcs @ [f]}

let rec merge_modules (env : env) (modules : (string * module_) list) starts m : module_' =
  match modules with
  | [] -> merge_start env starts m
  | (file, (m_in : module_))::modules' ->
    trace ("Merging (" ^ file ^ ")...");
    let ts =
      if !Flags.unchecked then [] else
      let tmodule = {empty_module with types = m_in.it.types} @@ m_in.at in
      let inst = Wasm.Eval.init tmodule [] in
      inst.Wasm.Instance.types
    in
    let env', cnt_in, ims' = merge_imports env file m_in ts m_in.it.imports empty_cnt [] in
    let env' = merge_defs env' cnt_in m_in in
    let starts' =
      match m_in.it.start with
      | None -> starts
      | Some st -> starts @ [Subst.start env'.subst st]
    in
    let m' =
      { types = m.types @ Subst.(list type_ env'.subst m_in.it.types);
        globals = m.globals @ Subst.(list global env'.subst m_in.it.globals);
        tables = m.tables @ Subst.(list table env'.subst m_in.it.tables);
        memories = m.memories @ Subst.(list memory env'.subst m_in.it.memories);
        funcs = m.funcs @ Subst.(list func env'.subst m_in.it.funcs);
        elems = m.elems @ Subst.(list elem env'.subst m_in.it.elems);
        datas = m.datas @ Subst.(list data env'.subst m_in.it.datas);
        imports = m.imports @ Subst.(list import env'.subst ims');
        exports = Subst.(list export env'.subst m_in.it.exports);  (* only last *)
        start = None;
      }
    in
    let env' = merge_exports env' file m_in ts m'.exports in
    merge_modules {env' with subst = Subst.empty} modules' starts' m'

let merge modules =
  let env, mems = resolve_modules empty_env modules [] in
  if List.length mems > 1 then begin
    error (List.hd mems) (
      "multiple modules define a memory: " ^ String.concat " " mems
    )
  end;
  merge_modules env modules [] empty_module @@ no_region
