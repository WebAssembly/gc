(* Graph Minimization *)

(* Implementation based on:
 *  Antti Valmari, Petri Lehtinen
 *  "Efficient minimization of DFAs with partial transition functions"
 *  Symposium on Theoretical Aspects of Computer Science (STACS), 2008
 *)

module Part =  (* generic partitions *)
struct
  type elem =
    { mutable loc : int;
      mutable set : int;
    }
  type set =
    { mutable first : int;
      mutable mid : int;
      mutable last : int;
    }
  type t =
    { mutable num : int;
      elems : int array;
      el : elem array;
      st : set array;
    }

  let make n : t =
    { num = 1;
      elems = Array.init n (fun i -> i);
      el = Array.init n (fun i -> {loc = i; set = 0});
      st = Array.init n (fun _ -> {first = 0; mid = 0; last = n});
    }

  let elem_set p e = p.el.(e).set
  let set_size p s = let sx = p.st.(s) in sx.last - sx.first
  let set_first p s = p.elems.(p.st.(s).first)

  let elem_next p e =
    let ex = p.el.(e) in
    if ex.loc + 1 >= p.st.(ex.set).last then -1 else p.elems.(ex.loc + 1)

  let elem_mark p e =
    let ex = p.el.(e) in
    let s = ex.set in
    let sx = p.st.(s) in
    let l = ex.loc in
    let m = sx.mid in
    if l >= m then begin
      assert (p.elems.(l) = e);
      let e' = p.elems.(m) in
      p.elems.(l) <- e';
      p.elems.(m) <- e;
      p.el.(e').loc <- l;
      ex.loc <- m;
      sx.mid <- m + 1;
    end

  let set_split p s =
    let sx = p.st.(s) in
    if sx.mid = sx.last then sx.mid <- sx.first;
    if sx.mid = sx.first then -1 else begin
      let n = p.num in
      p.num <- n + 1;
      let nx = p.st.(n) in
      nx.first <- sx.first;
      nx.mid <- sx.first;
      nx.last <- sx.mid;
      sx.first <- sx.mid;
      for l = nx.first to nx.last - 1 do p.el.(p.elems.(l)).set <- n done;
      n
    end

  let set_has_no_marks p s =
    let sx = p.st.(s) in
    sx.mid = sx.first

  let assert_valid p =
    let a = Array.make (Array.length p.elems) 0 in
    Array.iter (fun i -> a.(i) <- a.(i) + 1) p.elems;
    assert (Array.for_all ((=) 1) a);
    Array.iteri (fun e ex ->
      assert (p.elems.(ex.loc) = e);
      assert (ex.set < p.num);
    ) p.el;
    Array.iteri (fun s sx ->
      if s < p.num then begin
        assert (sx.first <= sx.mid);
        assert (sx.mid <= sx.last);
        assert (sx.first = 0 ||
          Array.exists (fun sx' -> sx'.last = sx.first) p.st);
        assert (sx.last = Array.length p.elems ||
          Array.exists (fun sx' -> sx'.first = sx.last) p.st);
      end
    ) p.st;
    true

  let print p =
    for s = 0 to p.num - 1 do
      let sx = p.st.(s) in
      if s > 0 then Printf.printf " , ";
      for i = sx.first to sx.last - 1 do
        if i = sx.mid then Printf.printf "."
        else if i > sx.first then Printf.printf " ";
        Printf.printf "%d" p.elems.(i)
      done;
      if sx.mid = sx.last then Printf.printf "."
    done
end

type edge_idx = int
type edge =
  { from : Vert.idx;
    pos : int;
    to_ : Vert.idx;
    mutable idx : edge_idx;
  }

let dummy_edge = {from = -1; pos = -1; to_ = -1; idx = -1}
let compare_edge_pos {pos = pos1; _} {pos = pos2; _} = compare pos1 pos2

let minimize (verts : Vert.t array) =
  let num_verts = Array.length verts in

  (* Initialise edge map *)
  let inedges = Array.make num_verts [] in
  let num_edges = ref 0 in
  let max_arity = ref (-1) in
  for v = 0 to num_verts - 1 do
    let pos = ref 0 in
    let succs = verts.(v).Vert.succs in
    for i = 0 to Array.length succs - 1 do
      let id = succs.(i) in
      if id < 0 then begin
        let w = -id-1 in
        inedges.(w) <- {from = v; pos = !pos; to_ = w; idx = -1} :: inedges.(w);
        incr pos
      end
    done;
    num_edges := !num_edges + !pos;
    max_arity := max !max_arity !pos;
  done;
  let e = ref 0 in
  let edges = Array.make !num_edges dummy_edge in
  for v = 0 to num_verts - 1 do
    List.iter (fun edge ->
      edges.(!e) <- edge; edge.idx <- !e; incr e
    ) inedges.(v)
  done;
(*
Printf.printf "[edges:";
Array.iteri Vert.(fun i edge -> Printf.printf " %d:%d[%d]->%d" i edge.from edge.pos edge.to_) edges;
Printf.printf "]\n%!";
*)

  (* Initialise data structures *)
  let blocks = Part.make num_verts in
  let splitters = Part.make !num_edges in

  (* Initialise blocks: partition by vertex label *)
  let labelmap = Hashtbl.create num_verts in
  for v = 0 to num_verts - 1 do
    let vert = verts.(v) in
    let key = (vert.Vert.label, vert.Vert.succs) in
    let vs =
      match Hashtbl.find_opt labelmap key with
      | None -> []
      | Some vs -> vs
    in Hashtbl.replace labelmap key (v::vs)
  done;
  let num_blocks, l = Hashtbl.fold
    (fun _ vs (s, l) ->
      let open Part in
      let sx = blocks.st.(s) in
      sx.first <- l;
      sx.mid <- l;
      let l' = List.fold_left
        (fun l v ->
          let ex = blocks.el.(v) in
          ex.loc <- l;
          ex.set <- s;
          blocks.elems.(l) <- v;
          l + 1
        ) l vs
      in
      sx.last <- l';
      (s + 1, l')
    ) labelmap (0, 0)
  in
  blocks.Part.num <- num_blocks;
  assert (l = num_verts);
  assert (Part.assert_valid blocks);

  (* Initialise splitters: partition by edge position and label *)
  let posmap = Array.make (!max_arity + 1) [] in
  for e = 0 to !num_edges - 1 do
    let pos = edges.(e).pos in
    posmap.(pos) <- e :: posmap.(pos);
  done;
  let s = ref (-1) in
  let l = ref 0 in
  let edge_block e = blocks.Part.el.(edges.(e).to_).Part.set in
  Array.iter (fun es ->
    if es = [] then () else
    let open Part in
    let by_block e1 e2 = compare (edge_block e1) (edge_block e2) in
    let es' = List.fast_sort by_block es in
    let b = ref (-1) in
    List.iter (fun e ->
      let b' = edge_block e in
      if b' <> !b then begin
        b := b';
        if !s <> -1 then splitters.st.(!s).last <- !l;
        incr s;
        let sx = splitters.st.(!s) in
        sx.first <- !l;
        sx.mid <- !l;
      end;
      let ex = splitters.el.(e) in
      ex.loc <- !l;
      ex.set <- !s;
      splitters.elems.(!l) <- e;
      incr l
    ) es'
  ) posmap;
  if !s <> -1 then splitters.Part.st.(!s).Part.last <- !l;
  splitters.Part.num <- !s + 1;
  assert (!l = !num_edges);
  assert (Part.assert_valid splitters);

  (* Auxiliary stacks *)
  let unready_splitters = Array.make !num_edges (-1) in
  let touched_splitters = Array.make !num_edges (-1) in
  let touched_blocks = Array.make num_verts (-1) in
  let unready_splitters_top = ref splitters.Part.num in
  let touched_splitters_top = ref 0 in
  let touched_blocks_top = ref 0 in

  for sp = 0 to splitters.Part.num - 1 do
    unready_splitters.(sp) <- sp
  done;

  (* Main loop *)
  while !unready_splitters_top <> 0 do
    decr unready_splitters_top;
    let sp = unready_splitters.(!unready_splitters_top) in
    let e = ref (Part.set_first splitters sp) in
    while !e <> -1 do
      let v = edges.(!e).from in
      let b = Part.elem_set blocks v in
      if Part.set_has_no_marks blocks b then begin
        touched_blocks.(!touched_blocks_top) <- b;
        incr touched_blocks_top
      end;
      Part.elem_mark blocks v;
      e := Part.elem_next splitters !e;
    done;
    while !touched_blocks_top <> 0 do
      decr touched_blocks_top;
      let b = touched_blocks.(!touched_blocks_top) in
      let b' = Part.set_split blocks b in
      if b' <> -1 then begin
        let b'' =
          if Part.set_size blocks b < Part.set_size blocks b' then b else b' in
        let v = ref (Part.set_first blocks b'') in
        while !v <> -1 do
          List.iter (fun edge ->
            let sp = Part.elem_set splitters edge.idx in
            if Part.set_has_no_marks splitters sp then begin
              touched_splitters.(!touched_splitters_top) <- sp;
              incr touched_splitters_top
            end;
            Part.elem_mark splitters edge.idx;
          ) inedges.(!v);
          v := Part.elem_next blocks !v;
        done;
        while !touched_splitters_top <> 0 do
          decr touched_splitters_top;
          let sp = touched_splitters.(!touched_splitters_top) in
          let sp' = Part.set_split splitters sp in
          if sp' <> -1 then begin
            unready_splitters.(!unready_splitters_top) <- sp';
            incr unready_splitters_top
          end
        done
      end
    done
  done;

  assert (Part.assert_valid blocks);
  assert (Part.assert_valid splitters);
  blocks, splitters
