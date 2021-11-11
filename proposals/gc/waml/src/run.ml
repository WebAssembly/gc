(* Errors & Tracing *)

exception WasmFormat of Source.region * string
exception Recursive of Source.region * exn * Printexc.raw_backtrace

let trace name = if !Flags.trace then print_endline ("-- " ^ name)

let error at category msg =
  trace ("Error: ");
  prerr_endline (Source.string_of_region at ^ ": " ^ category ^ ": " ^ msg);
  None

let rec handle f =
  try Some (f ()) with
  | Parse.Error (at, msg) -> error at "syntax error" msg
  | Typing.Error (at, msg) -> error at "type error" msg
  | Eval.Trap (at, msg) -> error at "runtime error" msg
  | Eval.Crash (at, msg) -> error at "crash" msg
  | Compile.NYI (at, msg) ->
    error at "compilation error" (msg ^ " not yet implemented")
  | Link.Error (at, msg) -> error at "linking error" msg
  | Wasm.Valid.Invalid (at, msg) ->
    error at "validation error (compilation bug)" msg
  | Wasm.Import.Unknown (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Link (at, msg) -> error at "link failure" msg
  | Wasm.Eval.Trap (at, msg) -> error at "runtime trap" msg
  | Wasm.Eval.Exhaustion (at, msg) -> error at "resource exhaustion" msg
  | Wasm.Eval.Crash (at, msg) -> error at "runtime crash" msg
  | WasmFormat (at, msg) -> error at "file format error" msg
  | Sys_error msg -> error Source.no_region "i/o error" msg
  | Recursive (at, exn, backtrace) ->
    ignore (error at "error while loading" "");
    handle (fun () -> Printexc.(raise_with_backtrace exn backtrace))


(* Input *)

(* Let's hope this is build-dependent enough *)
let marshal_tag () = Hashtbl.hash (Marshal.to_string handle [Marshal.Closures])
let marshal_conf () = Flags.(!box_modules, !headless)

let with_in_file open_in_mode file f =
  let ic = open_in_mode file in
  try
    let result = f ic in
    close_in ic;
    result
  with exn -> close_in ic; raise exn

let input_file file f =
  trace ("Loading (" ^ file ^ ")...");
  with_in_file open_in file (fun ic -> f (Lexing.from_channel ic))

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
    let result = f lexbuf in
    if result = None then Lexing.flush_input lexbuf;
    if Lexing.(lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len - 1) then
      continuing := false;
    loop ()
  in
  try loop () with End_of_file ->
    print_endline "";
    trace "Bye."

let read_binary_file file : Wasm.Ast.module_ * (Type.var list * Typing.env) =
  let file' = Filename.chop_extension file ^ ".wasm" in
  trace ("Reading (" ^ file ^ ")...");
  let bin = with_in_file open_in_bin file'
    (fun ic -> really_input_string ic (in_channel_length ic)) in
  trace "Decoding...";
  let m = Wasm.Decode.decode file' bin in
  let pos = Source.{no_pos with file = file'} in
  let at = Source.{left = pos; right = pos} in
  match Wasm.Decode.decode_custom (Wasm.Utf8.decode "waml-sig") file' bin with
  | [] ->
    raise (WasmFormat (at, "wasm binary is missing signature information"))
  | _::_::_ ->
    raise (WasmFormat (at, "wasm binary has duplicate signature information"))
  | [s] ->
    try
      let bs = Bytes.of_string s in
      if Marshal.from_string s 0 <> marshal_tag () then
        raise (WasmFormat (at, "wasm binary is from incompatible build or compilation options"));
      let off1 = Marshal.total_size bs 0 in
      if Marshal.from_string s off1 <> marshal_conf () then
        raise (WasmFormat (at, "wasm binary has incompatible language mode"));
      let off2 = off1 + Marshal.total_size bs off1 in
      trace "Decoding signature...";
      m, Marshal.from_string s off2
    with Failure _ ->
      raise (WasmFormat (at, "wasm binary has malformed signature information"))


(* Output *)

let with_out_file open_out_mode file f =
  let oc = open_out_mode file in
  try
    f oc; close_out oc
  with exn -> close_out oc; raise exn

let write_binary_file file m (stat_opt : (Type.var list * Typing.env) option) =
  let file' = file ^ ".wasm" in
  trace "Encoding...";
  let s1 = Wasm.Encode.encode m in
  let s2 =
    match stat_opt with
    | None -> ""
    | Some stat ->
      trace "Encoding signature...";
      let custom =
        Marshal.to_string (marshal_tag ()) [] ^
        Marshal.to_string (marshal_conf ()) [] ^
        Marshal.to_string stat [Marshal.Closures]
      in
      Wasm.Encode.encode_custom (Wasm.Utf8.decode "waml-sig") custom
  in
  trace ("Writing (" ^ file' ^ ")...");
  with_out_file open_out_bin file' (fun oc ->
    output_string oc s1;
    output_string oc s2;
  )

let write_textual_file file m =
  let file' = file ^ ".wat" in
  trace ("Writing (" ^ file' ^ ")...");
  with_out_file open_out file' (fun oc -> Wasm.Print.module_ oc !Flags.width m)

let write_file file m stat =
  let file' = Filename.chop_extension file in
  if !Flags.textual then
    write_textual_file file' m
  else
    write_binary_file file' m (Some stat)

let write_stdout m =
  trace "Printing Wasm...";
  Wasm.Print.module_ stdout !Flags.width m


(* Runtime System *)

let runtime_module : Wasm.Ast.module_ option ref = ref None
let runtime_instance : Wasm.Instance.module_inst option ref = ref None

let generate_runtime () =
  trace ("Compiling runtime system...");
  let runtime = Runtime.compile_runtime () in
  if !Flags.validate then begin
    trace "Validating runtime system...";
    Wasm.Valid.check_module runtime
  end;
  runtime_module := Some runtime;
  if not !Flags.headless then
  (
    trace ("Instantiating runtime system...");
    runtime_instance := Some (Wasm.Eval.init runtime [])
  )

let init () =
  if not !Flags.headless then generate_runtime ()

let compile_runtime file =
  if !runtime_module = None then generate_runtime ();
  let m = Option.get !runtime_module in
  match Filename.extension file with
  | ".wasm" -> write_binary_file (Filename.chop_extension file) m None; true
  | ".wat" -> write_textual_file (Filename.chop_extension file) m; true
  | ext -> prerr_endline (file ^ ": Unknown output file type"); false


(* Compilation pipeline *)

let frontend name lexbuf start env : Syntax.prog * (Type.typ * (Type.var list * Typing.env)) =
  trace "Parsing...";
  let prog = Parse.parse name lexbuf start in
  if !Flags.print_ast then begin
    trace "Abstract syntax:";
    Wasm.Sexpr.print !Flags.width (Arrange.prog prog);
  end;
  if !Flags.unchecked then prog, (Type.Tup [], ([], Env.empty)) else begin
    trace "Checking...";
    let t, bs, senv = Typing.check_prog env prog in
    prog, (t, (bs, senv))
  end

let backend prog : Wasm.Ast.module_ =
  trace "Compiling...";
  let wasm = Compile.compile_prog prog in
  if !Flags.validate then begin
    trace "Validating Wasm...";
    Wasm.Valid.check_module wasm
  end;
  wasm


(* Execution *)

let eval env prog =
  trace "Running...";
  let v, env' = Eval.eval_prog env prog in
  Printf.printf "%s" (Value.string_of_value v);
  env'

let exec wasm f =
  trace "Running Wasm...";
  let inst = Link.link wasm in
  f inst;
  match Wasm.Instance.export inst (Wasm.Utf8.decode "return") with
  | Some (Wasm.Instance.ExternGlobal glob) ->
    Printf.printf "%s" Wasm.(Value.string_of_value (Global.load glob))
  | _ -> ()


(* Registry *)

module Reg = Env.Map

type entry =
  { stat : Type.var list * Typing.env;
    dyn : Eval.env;
    inst : Wasm.Instance.module_inst option;
  }

let reg : entry Reg.t ref = ref Reg.empty

let register file stat dyn inst =
  reg := Reg.add file {stat; dyn; inst} !reg


(* Environment handling *)

type env = Typing.env * Eval.env

let env : env ref = ref (Env.empty, Env.empty)
let env_name = "*env*"

let inject_env senv prog =
  let open Source in
  let open Syntax in
  let Prog (imps, decs) = prog.it in
  if senv = Env.empty then prog else
  let imp = ImpD (env_name @@ prog.at, env_name) @@ prog.at in
  let var = PlainP (env_name @@ prog.at) @@ prog.at in
  let mod_ = VarM var @@ prog.at in
  let dec = InclD mod_ @@ prog.at in
  let prog' = Prog (imp :: imps, dec :: decs) @@ prog.at in
  imp.et <- Some senv;
  var.et <- Some (T.Str ([], senv));
  mod_.et <- Some (T.Str ([], senv));
  dec.et <- Some (T.Tup [], senv);
  prog'.et <- prog.et;
  prog'


(* Running *)

let run name lexbuf start =
  handle (fun () ->
    let (senv, denv) = !env in
    let prog, (t, ((bs, senv') as stat)) = frontend name lexbuf start senv in
    let denv' =
      if not !Flags.compile then
        eval denv prog
      else begin
        let wasm = backend (inject_env senv prog) in
        if !Flags.textual then write_stdout wasm;
        if !Flags.run then
          exec wasm (fun inst -> register env_name stat Env.empty (Some inst));
        Env.empty
      end
    in
    env := (Env.adjoin senv senv', Env.adjoin denv denv');
    let open Printf in
    if not !Flags.unchecked then begin
      printf "%s%s\n" (if not !Flags.run then "" else " : ") (Type.string_of_typ t);
      if !Flags.print_sig && senv' <> Env.empty then
        printf "%s\n" (Type.string_of_str senv')
    end
    else if !Flags.run then
      printf "\n"
  )

let run_file file : bool =
  input_file file (fun lexbuf -> run file lexbuf Parse.Prog) <> None

let run_string string : bool =
  input_string string (fun lexbuf -> run "string" lexbuf Parse.Prog) <> None

let run_stdin () =
  input_stdin (fun lexbuf -> run "stdin" lexbuf Parse.Repl)


(* Compilation *)

let compile name file lexbuf start =
  handle (fun () ->
    let prog, (_, stat) = frontend name lexbuf start Env.empty in
    if !Flags.compile then
      write_file file (backend prog) stat
  )

let compile_file file : bool =
  input_file file (fun lexbuf -> compile file file lexbuf Parse.Prog) <> None

let compile_string string file : bool =
  input_string file
    (fun lexbuf -> compile "string" file lexbuf Parse.Prog) <> None


(* Registry hooks *)

let load_file url at : entry =
  try
    if !Flags.prompt then
      print_endline ("// loading \"" ^ url ^ "\"");
    trace (String.make 60 '-');
    trace ("Loading import \"" ^ url ^ "\"...");
    let src_file = url ^ ".waml" in
    let wasm_file = url ^ ".wasm" in
    let stat, dyn, wasm_opt =
      if !Flags.compile && Sys.file_exists wasm_file then begin
        let wasm, stat = read_binary_file wasm_file in
        stat, Env.empty, Some wasm
      end
      else begin
        input_file src_file (fun lexbuf ->
          let prog, (_, stat) =
            frontend src_file lexbuf Parse.Prog Env.empty in
          if not !Flags.compile then begin
            trace "Running...";
            stat, snd (Eval.eval_prog Env.empty prog), None
          end
          else begin
            let wasm = backend prog in
            if not !Flags.prompt then
              write_file wasm_file wasm stat;
            stat, Env.empty, Some wasm
          end
        )
      end
    in
    let inst =
      if not !Flags.run || wasm_opt = None then None else begin
        trace "Linking...";
        Option.map Link.link wasm_opt
      end
    in
    let entry = {stat; dyn; inst} in
    trace ("Finished import \"" ^ url ^ "\".");
    trace (String.make 60 '-');
    entry
  with exn -> raise (Recursive (at, exn, Printexc.get_raw_backtrace ()))

let find_entry url at =
  if url = Runtime.module_name then
    {stat = ([], Env.empty); dyn = Env.empty; inst = !runtime_instance}
  else
    match Reg.find_opt url !reg with
    | Some entry -> entry
    | None ->
      let entry = load_file url at in
      reg := Reg.add url entry !reg;
      entry

let _ = Typing.get_env := fun at url -> (find_entry url at).stat
let _ = Eval.get_env := fun at url -> (find_entry url at).dyn
let _ = Link.get_inst := fun at url -> (find_entry url at).inst
