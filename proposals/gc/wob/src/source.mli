type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}
type ('a, 'b) phrase = {at : region; it : 'a; mutable et : 'b option}

val no_pos : pos
val no_region : region

val string_of_pos : pos -> string
val string_of_region : region -> string

val (@@) : 'a -> region -> ('a, 'b) phrase

val at : ('a, 'b) phrase -> region
val it : ('a, 'b) phrase -> 'a
val et : ('a, 'b) phrase -> 'b
