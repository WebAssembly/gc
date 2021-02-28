(* Errors & Tracing *)

module Abort = Error.Make ()
module IO = Error.Make ()

exception Abort = Abort.Error
exception IO = IO.Error

let trace name = if !Flags.trace then print_endline ("-- " ^ name)


(* Output *)

let write_binary_file file m =
  let file' = Filename.concat file "wasm" in
  trace ("Encoding (" ^ file' ^ ")...");
  let s = Wasm.Encode.encode m in
  let oc = open_out_bin file' in
  try
    trace "Writing...";
    output_string oc s;
    close_out oc
  with exn -> close_out oc; raise exn

let write_textual_file file m =
  let file' = Filename.concat file "wat" in
  trace ("Writing (" ^ file' ^ ")...");
  let oc = open_out file' in
  try
    Wasm.Print.module_ oc !Flags.width m;
    close_out oc
  with exn -> close_out oc; raise exn

let _write_file file m =
  let file' = Filename.chop_extension file in
  if !Flags.textual then
    write_textual_file file' m
  else
    write_binary_file file' m

let _write_stdout m =
  trace "Printing...";
  Wasm.Print.module_ stdout !Flags.width m


(* Input *)

let error at category msg =
  trace ("Error: ");
  prerr_endline (Source.string_of_region at ^ ": " ^ category ^ ": " ^ msg);
  false

let input name lexbuf start =
  try
    trace "Parsing...";
    let prog = Parse.parse name lexbuf start in
    (* TODO *)
    let v, _env = Eval.eval_prog Value.empty_env prog in
    Printf.printf "%s\n" (Value.string_of_value v);
(*
    trace "Running...";
    run script;
*)
    true
  with
  | Parse.Error (at, msg) -> error at "syntax error" msg
  | Eval.Trap (at, msg) -> error at "runtime error" msg
  | Eval.Crash (at, msg) -> error at "crash" msg
(*
  | Typing.Invalid (at, msg) -> error at "invalid module" msg
  | Import.Unknown (at, msg) -> error at "link failure" msg
*)
  | IO (at, msg) -> error at "i/o error" msg
  | Abort _ -> false

let input_file file =
  trace ("Loading (" ^ file ^ ")...");
  let ic = open_in file in
  try
    let lexbuf = Lexing.from_channel ic in
    let success = input file lexbuf Parse.Prog in
    close_in ic;
    success
  with exn -> close_in ic; raise exn

let input_string string =
  trace ("Running (\"" ^ String.escaped string ^ "\")...");
  let lexbuf = Lexing.from_string string in
  input "string" lexbuf Parse.Prog


let continuing = ref false

let lexbuf_stdin buf len =
  let prompt = if !continuing then "  " else "> " in
  print_string prompt; flush_all ();
  continuing := true;
  let rec loop i =
    if i = len then i else
    let ch = input_char stdin in
    Bytes.set buf i ch;
    if ch = '\n' then i + 1 else loop (i + 1)
  in
  let n = loop 0 in
  if n = 1 then continuing := false else trace "Parsing...";
  n

let input_stdin () =
  let lexbuf = Lexing.from_function lexbuf_stdin in
  let rec loop () =
    let success = input "stdin" lexbuf Parse.Repl in
    if not success then Lexing.flush_input lexbuf;
    if Lexing.(lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len - 1) then
      continuing := false;
    loop ()
  in
  try loop () with End_of_file ->
    print_endline "";
    trace "Bye."


(* Printing *)

(*
let indent s =
  let lines = List.filter ((<>) "") (String.split_on_char '\n' s) in
  String.concat "\n" (List.map ((^) "  ") lines) ^ "\n"

let print_module x_opt m =
  Printf.printf "module%s :\n%s%!"
    (match x_opt with None -> "" | Some x -> " " ^ x.it)
    (indent (Types.string_of_module_type (Ast.module_type_of m)))

let print_values vs =
  let ts = List.map Value.type_of_value vs in
  Printf.printf "%s : %s\n%!"
    (Value.string_of_values vs) (Types.string_of_stack_type ts)

let string_of_nan = function
  | CanonicalNan -> "nan:canonical"
  | ArithmeticNan -> "nan:arithmetic"

let type_of_result r =
  match r with
  | LitResult v -> Value.type_of_value v.it
  | NanResult n -> Types.NumType (Value.type_of_num n.it)
  | RefResult t -> Types.(RefType (NonNullable, t))
  | NullResult -> Types.(RefType (Nullable, ExternHeapType))

let string_of_result r =
  match r with
  | LitResult v -> Value.string_of_value v.it
  | NanResult nanop ->
    (match nanop.it with
    | Value.I32 _ | Value.I64 _ -> assert false
    | Value.F32 n | Value.F64 n -> string_of_nan n
    )
  | RefResult t -> Types.string_of_heap_type t
  | NullResult -> "null"

let string_of_results = function
  | [r] -> string_of_result r
  | rs -> "[" ^ String.concat " " (List.map string_of_result rs) ^ "]"

let print_results rs =
  let ts = List.map type_of_result rs in
  Printf.printf "%s : %s\n%!"
    (string_of_results rs) (Types.string_of_stack_type ts)
*)


(* Running *)

let run_file file = input_file file
let run_string string = input_string string
let run_stdin () = input_stdin ()


(* Compilation *)

let compile_file _ = failwith "compile_file"
let compile_string _ = failwith "compile_string"
