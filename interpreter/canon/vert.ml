(* Type Graph Representation: Vertices *)

type idx = int
type t =
  { mutable id : int;
    label : Label.t;
    succs : int array;  (* id of successor, or negative when within own SCC *)
    mutable inner : idx array;  (* index within own SCC for each succ id of -1 *)
  }

let dummy =
  { id = -1;
    label = Label.dummy;
    succs = [||];
    inner = [||];
  }

(* Verification *)

let assert_valid maxid maxvert vert =
let n = ref 0 in
  assert (vert.id < maxid);
  Array.iter (fun id ->
    if id >= 0 then assert (id < maxid);
    if id < 0 then assert (-id-1 < maxvert);
    if id < 0 then incr n;
  ) vert.succs;
  assert (!n = Array.length vert.inner);
  Array.iter (fun w ->
    assert (w >= 0);
    assert (w < maxvert);
  ) vert.inner;
  true

let assert_valid_graph maxid verts =
  Array.for_all (fun vert ->
    assert_valid maxid (Array.length verts) vert
  ) verts


(* Construction *)

let raw_id id = -id - 1
let is_raw_id id = id < 0

let make scc x dt : t =
  let open Label in
  let c = {scc; buf = Buffer.create 32; edges = []} in
  Label.def_label c dt;
  let succs = Array.of_list (List.rev c.edges) in
  let inner = ref [] in
  let n = ref 0 in
  Array.iteri (fun i id ->
    if id < 0 then inner := -id-1 :: !inner;
    if id < 0 then incr n
  ) succs;
  assert (!n = List.length !inner);
  let vert = {id = x; label = Buffer.contents c.buf; succs; inner = Array.of_list (List.rev !inner) } in
  assert (assert_valid Int.max_int Int.max_int vert);
  vert


(* Debugging aid *)

let print_graph verts =
  Array.iteri (fun v vert ->
    Printf.printf " %d = _%d(" v (Hashtbl.hash vert.label);
    let i = ref 0 in
    Array.iteri (fun j id ->
      if j > 0 then Printf.printf ", ";
      if id = -1
      then (Printf.printf "%d" vert.inner.(!i); incr i)
      else Printf.printf "#%d" id;
    ) vert.succs;
    Printf.printf ")\n%!"
  ) verts
