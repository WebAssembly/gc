let name = "waml"
let version = "0.1"

let banner () =
  print_endline (name ^ " " ^ version ^ " interpreter")

let usage = "Usage: " ^ name ^ " [option] [file ...]"
let help = ref (fun _ -> failwith "help")

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let argspec = Arg.align
[
  "-", Arg.Set Flags.prompt,
    " start interactive prompt (default if no files given)";
  "-r", Arg.Set Flags.interpret,
    " interpret input (default when interactive)";  (* TODO: for now *)
  "-c", Arg.Set Flags.compile,
    " compile input to Wasm (default when files given)";
  "-d", Arg.Set Flags.dry,
    " dry, do not run program" ^
    " (default when compiling non-interactively)";
  "-u", Arg.Set Flags.unchecked,
    " unchecked, do not perform type-checking (only without -c)";
  "-v", Arg.Set Flags.validate,
    " validate generated Wasm";
  "-a", Arg.Set Flags.print_ast,
    " output abstract syntac";
  "-s", Arg.Set Flags.print_sig,
    " print type signature (default when interactive)";
  "-b", Arg.Set Flags.boxed,
    " universal generics, box everything";
  "-p", Arg.Set Flags.parametric,
    " parametric generics, disallows casts (currently implied by -c)";
  "-x", Arg.Set Flags.textual,
    " output textual Wasm";
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

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec add_arg usage;
    if !args = [] then Flags.prompt := true;
    if !Flags.prompt then Flags.interpret := true;  (* TODO: for now *)
    if !Flags.compile then Flags.unchecked := false;
    if !Flags.compile then Flags.parametric := true;
    if !Flags.interpret then
    (
      List.iter (fun arg -> if not (Run.run_file arg) then exit 1) !args;
      if !Flags.prompt then
      (
        Flags.print_sig := true;
        banner ();
        Run.run_stdin ();
      )
    )
    else
      List.iter (fun arg -> if not (Run.compile_file arg) then exit 1) !args;
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
