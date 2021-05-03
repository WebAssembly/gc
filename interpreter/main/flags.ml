let interactive = ref false
let trace = ref false
let unchecked = ref false
let print_sig = ref false
let dry = ref false
let width = ref 80
let harness = ref true

let canon : [`CanonMin | `CanonGlobal | `CanonIncr] option ref = ref None
let canon_random = ref (-1)
let canon_seed = ref (-1)
let canon_verify = ref false
