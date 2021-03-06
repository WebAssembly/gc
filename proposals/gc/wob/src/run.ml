(* Errors & Tracing *)

exception Recursive of string * exn * Printexc.raw_backtrace

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
  | Sys_error msg -> error Source.no_region "i/o error" msg
  | Recursive (file, exn, backtrace) ->
    prerr_endline (file ^ ": error while loading:");
    handle (fun () -> Printexc.(raise_with_backtrace exn backtrace))


(* Input *)

(* Let's hope this is build-dependen enough *)
let marshal_tag = Hashtbl.hash (Marshal.to_string handle [Marshal.Closures])

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

let read_binary_file file =
  let file' = Filename.chop_extension file ^ ".wasm" in
  trace ("Reading (" ^ file ^ ")...");
  let bin = with_in_file open_in_bin file'
    (fun ic -> really_input_string ic (in_channel_length ic)) in
  trace "Decoding...";
  Wasm.Decode.decode file' bin


let read_sig_file file =
  let file' = Filename.chop_extension file ^ ".wos" in
  with_in_file open_in_bin file' (fun ic ->
    let tag = Marshal.from_channel ic in
    if tag <> marshal_tag then
      raise (Sys_error "incompatible signature file");
    Marshal.from_channel ic
  )


(* Output *)

let with_out_file open_out_mode file f =
  let oc = open_out_mode file in
  try
    f oc; close_out oc
  with exn -> close_out oc; raise exn

let write_binary_file file m =
  let file' = file ^ ".wasm" in
  trace "Encoding...";
  let s = Wasm.Encode.encode m in
  trace ("Writing (" ^ file' ^ ")...");
  with_out_file open_out_bin file' (fun oc -> output_string oc s)

let write_textual_file file m =
  let file' = file ^ ".wat" in
  trace ("Writing (" ^ file' ^ ")...");
  with_out_file open_out file' (fun oc -> Wasm.Print.module_ oc !Flags.width m)

let write_file file m =
  let file' = Filename.chop_extension file in
  if !Flags.textual then
    write_textual_file file' m
  else
    write_binary_file file' m

let write_stdout m =
  trace "Printing Wasm...";
  Wasm.Print.module_ stdout !Flags.width m

let write_sig_file file stat =
  let file' = Filename.chop_extension file ^ ".wos" in
  with_out_file open_out_bin file' (fun oc ->
    Marshal.to_channel oc marshal_tag [];
    Marshal.to_channel oc stat [Marshal.Closures]
  )


(* Compilation pipeline *)

let frontend name lexbuf start env : Syntax.prog * (Type.typ * Typing.env) =
  trace "Parsing...";
  let prog = Parse.parse name lexbuf start in
  if !Flags.print_ast then
    Wasm.Sexpr.print !Flags.width (Arrange.prog prog);
  if !Flags.unchecked then prog, (Type.Bot, Env.empty) else begin
    trace "Checking...";
    prog, Typing.check_prog env prog
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
  Printf.printf "%s" (Value.to_string v);
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
  { stat : Typing.env;
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
  let senv' = Env.fold_vals (fun x st senv' ->
    Env.remove_typ (x @@ st.at) senv') senv senv in
  let ys = Env.fold_typs (fun y kc ys -> (y @@ kc.at)::ys) senv' [] in
  let nos = Env.fold_typs (fun _ _ nos -> None::nos) senv' [] in
  let xs = Env.fold_vals (fun x st xs -> (x @@ st.at)::xs) senv [] in
  let sts = Env.fold_vals (fun _ st sts -> Some (st.it) :: sts) senv [] in
  let imp = ImpD (None, ys @ xs, env_name) @@ prog.at in
  let prog' = Prog (imp :: imps, decs) @@ prog.at in
  imp.et <- Some (nos @ sts);
  prog'.et <- prog.et;
  prog'


(* Running *)

let run name lexbuf start =
  handle (fun () ->
    let (senv, denv) = !env in
    let prog, (t, senv') = frontend name lexbuf start senv in
    let denv' =
      if not !Flags.compile then
        eval denv prog
      else begin
        let wasm = backend (inject_env senv prog) in
        if !Flags.textual then write_stdout wasm;
        if not !Flags.dry then
          exec wasm (fun inst -> register env_name senv' Env.empty (Some inst));
        Env.empty
      end
    in
    env := (Env.adjoin senv senv', Env.adjoin denv denv');
    let open Printf in
    if not !Flags.unchecked then begin
      printf "%s%s\n" (if !Flags.dry then "" else " : ") (Type.to_string t);
      if !Flags.print_sig then begin
        Env.iter_typs (fun x kc ->
          let (k, c) = kc.Source.it in
          let a = Char.code 'A' in
          let ys = List.init k (fun i -> String.make 1 (Char.chr (a + i))) in
          printf "type %s" x;
          if k > 0 then printf "<%s>" (String.concat ", " ys);
          printf " = %s\n" (Type.to_string (c (List.map Type.var ys)))
        ) senv';
        Env.iter_vals (fun x st ->
          printf "%s : %s\n" x (Type.to_string (snd st.Source.it))
        ) senv'
      end
    end
    else if not !Flags.dry then
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
    if !Flags.compile then begin
      let wasm = backend prog in
      write_file file wasm;
      write_sig_file file (stat : Typing.env);
    end
  )

let compile_file file : bool =
  input_file file (fun lexbuf -> compile file file lexbuf Parse.Prog) <> None

let compile_string string file : bool =
  input_string file
    (fun lexbuf -> compile "string" file lexbuf Parse.Prog) <> None


(* Registry hooks *)

let load_file url : entry =
  try
    trace (String.make 60 '-');
    trace ("Loading import \"" ^ url ^ "\"...");
    let src_file = url ^ ".wob" in
    let sig_file = url ^ ".wos" in
    let wasm_file = url ^ ".wasm" in
    let entry =
      if
        !Flags.compile && Sys.file_exists sig_file &&
        (!Flags.dry || Sys.file_exists wasm_file)
      then begin
        let stat = read_sig_file sig_file in
        let inst =
          if !Flags.dry then None else
          Some (Link.link (read_binary_file wasm_file))
        in {stat; dyn = Env.empty; inst}
      end
      else begin
        input_file src_file (fun lexbuf ->
          let prog, (_, stat) = frontend src_file lexbuf Parse.Prog Env.empty in
          let dyn, inst =
            if not !Flags.compile then
              snd (Eval.eval_prog Env.empty prog), None
            else
              Env.empty,
              if !Flags.dry then None else Some (Link.link (backend prog))
          in {stat; dyn; inst}
        )
      end
    in
    trace ("Finished import \"" ^ url ^ "\".");
    trace (String.make 60 '-');
    entry
  with exn -> raise (Recursive (url, exn, Printexc.get_raw_backtrace ()))

let find_entry url =
  match Reg.find_opt url !reg with
  | Some entry -> entry
  | None ->
    let entry = load_file url in
    reg := Reg.add url entry !reg;
    entry

let _ = Typing.get_env := fun url -> (find_entry url).stat
let _ = Eval.get_env := fun url -> (find_entry url).dyn
let _ = Link.get_inst := fun url -> (find_entry url).inst
