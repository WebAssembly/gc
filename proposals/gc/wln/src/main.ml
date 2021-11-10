let name = "wln"
let version = "0.2"

let banner () =
  print_endline (name ^ " " ^ version ^ " linker")

let usage = "Usage: " ^ name ^ " [option] file ... -o file"
let help = ref (fun _ -> failwith "help")

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let outfile = ref ""
let argspec = Arg.align
[
  "-o", Arg.Set_string outfile,
    " output file name (.wasm or .wat)";
  "-u", Arg.Set Flags.unchecked,
    " do not check import/export types";
  "-v", Arg.Set Flags.validate,
    " validate input and output Wasm files";
  "-r", Arg.Set Flags.unresolved,
    " show unresolved imports";
  "-w", Arg.Int (fun n -> Flags.width := n),
    " configure text output width (default is 80)";
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
    if !outfile = "" then !help ();
    Link.link_files !args !outfile
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
