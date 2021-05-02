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
  let vert = {id = raw_id x; label = Buffer.contents c.buf; succs} in
  assert (assert_valid Int.max_int Int.max_int vert);
  vert

let graph dta : t array =
  Array.mapi (fun x dt -> make IntSet.empty x dt) dta

let graph_of_scc dta scc dtamap sccmap : t array =
  let num_verts = IntSet.cardinal scc in
  let verts = Array.make num_verts dummy in
  let v = ref 0 in
  IntSet.iter (fun x ->
    sccmap.(x) <- !v;
    verts.(!v) <- make scc x dta.(x); incr v
  ) scc;
  for v = 0 to num_verts - 1 do
    let vert = verts.(v) in
    for i = 0 to Array.length vert.succs - 1 do
      let x = vert.succs.(i) in
      vert.succs.(i) <- if x >= 0 then dtamap.(x) else -sccmap.(-x-1)-1
    done
  done;
  verts


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
