type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}
type ('a, 'b) phrase = {at : region; it : 'a; mutable et : 'b option}

let (@@) x region = {it = x; at = region; et = None}

let it phrase = phrase.it
let at phrase = phrase.at
let et phrase = Option.get phrase.et


(* Positions and regions *)

let no_pos = {file = ""; line = 0; column = 0}
let no_region = {left = no_pos; right = no_pos}

let string_of_pos pos =
  if pos.line = -1 then
    Printf.sprintf "0x%x" pos.column
  else
    string_of_int pos.line ^ "." ^ string_of_int (pos.column + 1)

let string_of_region r =
  r.left.file ^ ":" ^ string_of_pos r.left ^
  (if r.right = r.left then "" else "-" ^ string_of_pos r.right)
