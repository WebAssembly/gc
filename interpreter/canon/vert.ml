(* Type Graph Representation: Vertices *)

type idx = int
type t =
  { mutable id : int;
    label : Label.t;
    succs : int array;  (* id of successor, or -1 when within own SCC *)
    mutable inner : idx array;  (* index within own SCC for each succ id of -1 *)
  }

let dummy =
  { id = -1;
    label = Label.dummy;
    succs = [||];
    inner = [||];
  }

let raw_id id = -id - 1
let is_raw_id id = id < 0

let make scc x dt : t =
  let open Label in
  let c = {scc; buf = Buffer.create 32; ext = []; rec_ = []} in
  Label.def_label c dt;
  { id = x;
    label = Buffer.contents c.buf;
    succs = Array.of_list (List.rev c.ext);
    inner = Array.of_list (List.rev c.rec_);
  }


(* Verification *)

let assert_valid maxid maxvert vert =
  let n = ref 0 in
  assert (vert.id < maxid);
  Array.iter (fun id ->
    assert (id = -1 || id >= 0);
    assert (id < maxid);
    if id = -1 then incr n;
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
