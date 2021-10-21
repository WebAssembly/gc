(* Errors & Tracing *)

let trace name = if !Flags.trace then print_endline ("-- " ^ name)

let error msg =
  trace ("Error: ");
  prerr_endline msg;
  exit 1

let wasm_error at category msg =
  error (Wasm.Source.string_of_region at ^ ": " ^ category ^ ": " ^ msg)

let handle f x =
  try f x with
  | Sys_error msg -> error msg
  | Merge.Mismatch (file, msg) -> error (file ^ ": " ^ msg)
  | Wasm.Decode.Code (at, msg) -> wasm_error at "decoding error" msg
  | Wasm.Parse.Syntax (at, msg) -> wasm_error at "syntax error" msg
  | Wasm.Valid.Invalid (at, msg) -> wasm_error at "validation error" msg


(* Input *)

let with_in_file open_in_mode file f =
  let ic = open_in_mode file in
  try
    let result = f ic in
    close_in ic;
    result
  with exn -> close_in ic; raise exn

let read_binary_file file =
  trace ("Reading (" ^ file ^ ")...");
  let bin = with_in_file open_in_bin file
    (fun ic -> really_input_string ic (in_channel_length ic)) in
  trace "Decoding...";
  Wasm.Decode.decode file bin

let read_textual_file file =
  trace ("Reading (" ^ file ^ ")...");
  let src = with_in_file open_in file
    (fun ic -> really_input_string ic (in_channel_length ic)) in
  trace "Parsing...";
  Wasm.Parse.string_to_module src

let read_file file =
  match Filename.extension file with
  | ".wasm" -> read_binary_file file
  | ".wat" -> read_textual_file file
  | _ -> raise (Sys_error (file ^ ": Unknown input file type"))


(* Output *)

let with_out_file open_out_mode file f =
  let oc = open_out_mode file in
  try
    f oc; close_out oc
  with exn -> close_out oc; raise exn

let write_binary_file file m =
  trace "Encoding...";
  let s = Wasm.Encode.encode m in
  trace ("Writing (" ^ file ^ ")...");
  with_out_file open_out_bin file (fun oc -> output_string oc s)

let write_textual_file file m =
  trace ("Writing (" ^ file ^ ")...");
  with_out_file open_out file (fun oc -> Wasm.Print.module_ oc !Flags.width m)

let write_file file m =
  if !Flags.validate then begin
    trace "Validating...";
    Wasm.Valid.check_module m
  end;
  match Filename.extension file with
  | ".wasm" -> write_binary_file file m
  | ".wat" -> write_textual_file file m
  | _ -> raise (Sys_error (file ^ ": Unknown output file type"))


(* Linking *)

module Set = Set.Make(String)

let link_files infiles outfile =
  let modules =
    List.map (fun file ->
      let m = handle read_file file in
      if !Flags.validate then begin
        trace "Validating...";
        handle Wasm.Valid.check_module m
      end;
      (file, m)
    ) infiles
  in
  let m = handle Merge.merge modules in
  if !Flags.validate then begin
    trace "Validating result...";
    handle Wasm.Valid.check_module m
  end;
  trace "Writing result...";
  handle (write_file outfile) m;
  let open Wasm.Source in
  let open Wasm.Ast in
  if !Flags.unresolved && m.it.imports <> [] then begin
    let names =
      List.fold_left (fun s im ->
        Set.add (Wasm.Utf8.encode im.it.module_name) s
      ) Set.empty m.it.imports
    in
    Printf.printf "Unresolved import modules:\n";
    Set.iter (Printf.printf "  %s\n") names
  end
