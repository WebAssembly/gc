let name = "wob"
let version = "0.1"

let banner () =
  print_endline (name ^ " " ^ version ^ " interpreter")

let usage = "Usage: " ^ name ^ " [option] [file ...]"

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let argspec = Arg.align
[
  "-", Arg.Set Flags.interactive,
    " run interactively (default if no files given)";
  "-r", Arg.Clear Flags.compiled,
    " interpret";
  "-c", Arg.Set Flags.compiled,
    " compile (default when files given)";
  "-x", Arg.Set Flags.textual,
    " output textual Wasm";
  "-w", Arg.Int (fun n -> Flags.width := n),
    " configure output width (default is 80)";
  "-d", Arg.Set Flags.dry, " dry, do not run program";
  "-u", Arg.Set Flags.unchecked, " unchecked, do not perform validation";
  "-s", Arg.Set Flags.print_sig, " print type signature";
  "-v", Arg.Unit banner, " show version";
  "-t", Arg.Set Flags.trace, " trace execution";
]

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec add_arg usage;
    if not !Flags.compiled || !Flags.interactive || !args = [] then
    (
      List.iter (fun arg -> if not (Run.run_file arg) then exit 1) !args;
      if !Flags.interactive || !args = [] then
      (
        Flags.print_sig := true;
        Flags.textual := true;
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
