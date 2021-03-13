open Wasm.Source
open Wasm.Ast

exception Error of Source.region * string

let get_inst = ref (fun _ _ -> failwith "get_inst")

let link_import im =
  let {module_name; item_name; idesc} = im.it in
  let mname = Wasm.Utf8.encode module_name in
  let name = Wasm.Utf8.encode item_name in
  match !get_inst im.at mname with
  | None -> raise (Error (im.at, "unknown module \"" ^ mname ^ "\""))
  | Some inst ->
    match Wasm.Instance.export inst item_name with
    | Some ext -> ext
    | None ->
      raise (Error (im.at, "unknown item \"" ^ name ^ "\" in \"" ^ mname ^ "\""))

let link module_ =
  Wasm.Eval.init module_ (List.map link_import module_.it.imports)
