(* A growable array type *)

type 'a t = 'a array ref

let make n x = ref (Array.make n x)
let get t i = (!t).(i)
let set t i x = (!t).(i) <- x
let size t = Array.length !t

let grow t n x =
  let t' = Array.make (Array.length !t + n) x in
  Array.blit !t 0 t' 0 (Array.length !t);
  t := t'

let really_set t i x =
  let n = Array.length !t in
  if i >= n then grow t (max 10 n) x else set t i x
