let name = "wob"
let version = "0.2"

let banner () =
  print_endline (name ^ " " ^ version ^ " interpreter")

let usage = "Usage: " ^ name ^ " [option] [file ...]"
let help = ref (fun _ -> failwith "help")

let args = ref []
let gens = ref []
let add_list xs x = xs := !xs @ [x]

let quote s = "\"" ^ String.escaped s ^ "\""

let argspec = Arg.align
[
  "-", Arg.Set Flags.prompt,
    " start interactive prompt (default if no files given)";
  "-r", Arg.Set Flags.run,
    " run input (default when interactive or not compiling)";
  "-i", Arg.Set Flags.interpret,
    " run with interpreter (default when interactive, for now)";
  "-c", Arg.Set Flags.compile,
    " compile input to Wasm (default when files given)";
  "-n", Arg.Set Flags.headless,
    " no runtime system, compile headless";
  "-g", Arg.String (add_list gens),
    " generate runtime system";
  "-u", Arg.Set Flags.unchecked,
    " unchecked, do not perform type-checking (only without -c)";
  "-v", Arg.Set Flags.validate,
    " validate generated Wasm";
  "-x", Arg.Set Flags.textual,
    " produce textual Wasm";
  "-a", Arg.Set Flags.print_ast,
    " output abstract syntac";
  "-s", Arg.Set Flags.print_sig,
    " print type signature (default when interactive)";
  "-b", Arg.Set Flags.boxed,
    " universal generics, box everything";
  "-p", Arg.Set Flags.parametric,
    " parametric generics, disallows casts";
  "-w", Arg.Int (fun n -> Flags.width := n),
    " configure output width (default is 80)";
  "-t", Arg.Set Flags.trace,
    " trace execution";
  "-h", Arg.Unit (fun () -> !help ()),
    " show this list of options";
  "-help", Arg.Unit (fun () -> !help ()), "";
  "--help", Arg.Unit (fun () -> !help ()), "";
]

let () = help := fun () -> Arg.usage argspec usage; exit 0

let io f file =
  try
    if not (f file) then exit 1
  with Sys_error msg ->
    prerr_endline msg; exit 1

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec (add_list args) usage;
    if !args = [] && !gens = [] then Flags.prompt := true;
    if !Flags.prompt || not !Flags.compile then Flags.run := true;
    if !Flags.prompt then Flags.interpret := true;  (* TODO: for now *)
    if !Flags.compile then Flags.unchecked := false;
    Run.init ();
    List.iter (io Run.compile_runtime) !gens;
    if !Flags.run then
    (
      List.iter (io Run.run_file) !args;
      if !Flags.prompt then
      (
        Flags.print_sig := true;
        banner ();
        Run.run_stdin ();
      )
    )
    else
      List.iter (io Run.compile_file) !args;
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
