type pos = Wasm.Source.pos = {file : string; line : int; column : int}
type region = Wasm.Source.region = {left : pos; right : pos}
type ('a, 'b) phrase = {at : region; it : 'a; mutable et : 'b option}

let (@@) x region = {it = x; at = region; et = None}

let it phrase = phrase.it
let at phrase = phrase.at
let et phrase = Option.get phrase.et

let map_it f phrase = {phrase with it = f phrase.it}
let map_et f phrase = {phrase with et = Option.map f phrase.et}

let compare_by_region phrase1 phrase2 = compare phrase1.at phrase2.at


(* Positions and regions *)

let no_pos = {file = ""; line = 0; column = 0}
let no_region = {left = no_pos; right = no_pos}

let span r1 r2 = {left = r1.left; right = r2.right}

let string_of_pos pos =
  if pos.line = -1 then
    Printf.sprintf "0x%x" pos.column
  else
    string_of_int pos.line ^ "." ^ string_of_int (pos.column + 1)

let string_of_region r =
  r.left.file ^ ":" ^ string_of_pos r.left ^
  (if r.right = r.left then "" else "-" ^ string_of_pos r.right)
