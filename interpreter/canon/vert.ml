(* Type Graph Representation: Vertices *)

type idx = int
type t =
  { mutable id : int;
    label : Label.t;
    succs : int array;  (* id of successor, or negative when within own SCC *)
  }

let dummy =
  { id = -1;
    label = Label.dummy;
    succs = [||];
  }

(* Verification *)

let assert_valid maxid maxvert vert =
  assert (vert.id < maxid);
  Array.iter (fun id ->
    if id >= 0 then assert (id < maxid)
    else assert (-id-1 < maxvert)
  ) vert.succs;
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
  let vert = {id = x; label = Buffer.contents c.buf; succs} in
  assert (assert_valid Int.max_int Int.max_int vert);
  vert


(* Debugging aid *)

let print_graph verts =
  Array.iteri (fun v vert ->
    Printf.printf " %d = _%d(" v (Hashtbl.hash vert.label);
    Array.iteri (fun j id ->
      if j > 0 then Printf.printf ", ";
      if id < 0
      then Printf.printf "%d" (-id-1)
      else Printf.printf "#%d" id;
    ) vert.succs;
    Printf.printf ")\n%!"
  ) verts
