exception Abort of Source.region * string
exception IO of Source.region * string

val run_string : string -> bool
val run_file : string -> bool
val run_stdin : unit -> unit

val compile_string : string -> bool
val compile_file : string -> bool
