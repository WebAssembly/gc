let name = "waml"
let version = "0.1"

let banner () =
  print_endline (name ^ " " ^ version ^ " interpreter")

let usage = "Usage: " ^ name ^ " [option] [file ...]"
let help = ref (fun _ -> failwith "help")

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let box_all b =
  Flags.box_locals := b;
  Flags.box_globals := b;
  Flags.box_modules := b;
  Flags.box_temps := b;
  Flags.box_scrut := b

let default_if b = if b then " (default)" else ""

let argspec = Arg.align
[
  "-", Arg.Set Flags.prompt,
    " start interactive prompt (default if no files given)";
  "-r", Arg.Set Flags.interpret,
    " interpret input";
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
  "-blocals", Arg.Set Flags.box_locals,
    " box locals" ^ default_if !Flags.box_locals;
  "-bglobals", Arg.Set Flags.box_globals,
    " box globals" ^ default_if !Flags.box_globals;
  "-bmodules", Arg.Set Flags.box_modules,
    " box modules" ^ default_if !Flags.box_modules;
  "-btemps", Arg.Set Flags.box_temps,
    " box temporaries" ^ default_if !Flags.box_temps;
  "-bscrut", Arg.Set Flags.box_scrut,
    " box pattern scrutinees" ^ default_if !Flags.box_scrut;
  "-ball", Arg.Unit (fun () -> box_all true),
    " box all";
  "-ublocals", Arg.Clear Flags.box_locals,
    " unbox locals" ^ default_if (not !Flags.box_locals);
  "-ubglobals", Arg.Clear Flags.box_globals,
    " unbox globals" ^ default_if (not !Flags.box_globals);
  "-ubmodules", Arg.Clear Flags.box_modules,
    " unbox modules" ^ default_if (not !Flags.box_modules);
  "-ubtemps", Arg.Clear Flags.box_temps,
    " unbox temporaries" ^ default_if (not !Flags.box_temps);
  "-ubscrut", Arg.Clear Flags.box_scrut,
    " unbox pattern scrutinees" ^ default_if (not !Flags.box_scrut);
  "-uball", Arg.Unit (fun () -> box_all false),
    " unbox all";
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
    if !Flags.compile then Flags.unchecked := false;
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
