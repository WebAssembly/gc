val init : unit -> unit

val run_string : string -> bool
val run_file : string -> bool
val run_stdin : unit -> unit

val compile_string : string -> string -> bool
val compile_file : string -> bool

val compile_runtime : string -> bool
