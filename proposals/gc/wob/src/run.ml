(* Errors & Tracing *)

let trace name = if !Flags.trace then print_endline ("-- " ^ name)

let error at category msg =
  trace ("Error: ");
  prerr_endline (Source.string_of_region at ^ ": " ^ category ^ ": " ^ msg);
  false

let handle f : bool =
  try f (); true with
  | Parse.Error (at, msg) -> error at "syntax error" msg
  | Typing.Error (at, msg) -> error at "type error" msg
  | Eval.Trap (at, msg) -> error at "runtime error" msg
  | Eval.Crash (at, msg) -> error at "crash" msg
  | Compile.NYI (at, msg) ->
    error at "compilation error" (msg ^ " not yet implemented")
  | Wasm.Valid.Invalid (at, msg) ->
    error at "validation error (compilation bug)" msg
  | Wasm.Import.Unknown (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Link (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Trap (at, msg) -> error at "runtime trap" msg
  | Wasm.Eval.Exhaustion (at, msg) -> error at "resource exhaustion" msg
  | Wasm.Eval.Crash (at, msg) -> error at "runtime crash" msg
  | Sys_error msg -> error Source.no_region "i/o error" msg


(* Input *)

let input_file file f =
  trace ("Loading (" ^ file ^ ")...");
  match open_in file with
  | exception Sys_error msg -> error Source.no_region "i/o error" msg
  | ic ->
    try
      let success = f (Lexing.from_channel ic) in
      close_in ic;
      success
    with exn -> close_in ic; raise exn

let input_string string f =
  f (Lexing.from_string string)


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

let input_stdin f =
  let lexbuf = Lexing.from_function lexbuf_stdin in
  let rec loop () =
    let success = f lexbuf in
    if not success then Lexing.flush_input lexbuf;
    if Lexing.(lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len - 1) then
      continuing := false;
    loop ()
  in
  try loop () with End_of_file ->
    print_endline "";
    trace "Bye."


(* Output *)

let write_binary_file file m =
  let file' = file ^ ".wasm" in
  trace ("Encoding (" ^ file' ^ ")...");
  let s = Wasm.Encode.encode m in
  let oc = open_out_bin file' in
  try
    trace "Writing...";
    output_string oc s;
    close_out oc
  with exn -> close_out oc; raise exn

let write_textual_file file m =
  let file' = file ^ ".wat" in
  trace ("Writing (" ^ file' ^ ")...");
  let oc = open_out file' in
  try
    Wasm.Print.module_ oc !Flags.width m;
    close_out oc
  with exn -> close_out oc; raise exn

let write_file file m =
  let file' = Filename.chop_extension file in
  if !Flags.textual then
    write_textual_file file' m
  else
    write_binary_file file' m

let write_stdout m =
  trace "Printing Wasm...";
  Wasm.Print.module_ stdout !Flags.width m


(* Compilation pipeline *)

let frontend name lexbuf start : Syntax.prog * Type.typ option =
  trace "Parsing...";
  let prog = Parse.parse name lexbuf start in
  let t_opt =
    if !Flags.unchecked then None else begin
      trace "Checking...";
      let t, _env = Typing.check_prog Typing.initial_env prog in
      Some t
    end
  in
  prog, t_opt

let backend prog : Wasm.Ast.module_ =
  trace "Compiling...";
  let wasm = Compile.compile_prog prog in
  if !Flags.validate then begin
    trace "Validating Wasm...";
    Wasm.Valid.check_module wasm
  end;
  wasm


(* Execution *)

let eval prog =
  trace "Running...";
  let v, _env = Eval.eval_prog Eval.initial_env prog in
  Printf.printf "%s" (Value.to_string v)

let exec wasm =
  trace "Running Wasm...";
  let open Wasm in
  let inst = Eval.init wasm [] in
  List.iter (fun (name, extern) ->
    match extern with
    | Instance.ExternGlobal glob when name = Utf8.decode "return" ->
      Printf.printf "%s" (Value.string_of_value (Global.load glob))
    | _ -> ()
  ) inst.Instance.exports


(* Running *)

let run name lexbuf start =
  handle (fun () ->
    let prog, t_opt = frontend name lexbuf start in
    if not !Flags.compile then
      eval prog
    else begin
      let wasm = backend prog in
      if !Flags.textual then write_stdout wasm;
      if not !Flags.dry then exec wasm
    end;
    (match t_opt, not !Flags.dry with
    | Some t, b ->
      Printf.printf "%s%s\n" (if b then " : " else "") (Type.to_string t)
    | None, b ->
      if b then Printf.printf "\n"
    )
  )

let run_file file : bool =
  input_file file (fun lexbuf -> run file lexbuf Parse.Prog)

let run_string string : bool =
  input_string string (fun lexbuf -> run "string" lexbuf Parse.Prog)

let run_stdin () =
  input_stdin (fun lexbuf -> run "stdin" lexbuf Parse.Repl)


(* Compilation *)

let compile name file lexbuf start =
  handle (fun () ->
    let prog, t_opt = frontend name lexbuf start in
    if !Flags.compile then begin
      let wasm = backend prog in
      write_file file wasm
    end
  )

let compile_file file : bool =
  input_file file (fun lexbuf -> compile file file lexbuf Parse.Prog)

let compile_string string file : bool =
  input_string file (fun lexbuf -> compile "string" file lexbuf Parse.Prog)
