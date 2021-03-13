type pos = Wasm.Source.pos = {file : string; line : int; column : int}
type region = Wasm.Source.region = {left : pos; right : pos}
type ('a, 'b) phrase = {at : region; it : 'a; mutable et : 'b option}

val no_pos : pos
val no_region : region

val span : region -> region -> region

val string_of_pos : pos -> string
val string_of_region : region -> string

val (@@) : 'a -> region -> ('a, 'b) phrase

val at : ('a, 'b) phrase -> region
val it : ('a, 'b) phrase -> 'a
val et : ('a, 'b) phrase -> 'b

val map_it : ('a1 -> 'a2) -> ('a1, 'b) phrase -> ('a2, 'b) phrase
val map_et : ('b1 -> 'b2) -> ('a, 'b1) phrase -> ('a, 'b2) phrase

val compare_by_region : ('a, 'b) phrase -> ('a, 'b) phrase -> int
