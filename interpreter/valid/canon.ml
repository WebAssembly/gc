module T = Types

module Set = Set.Make(Int)

type scc_vert =
  { mutable index : int;
    mutable low : int;
    mutable onstack : bool;
  }

(* Tarjan's SCC algorithm *)
let scc_deftypes (dta : T.def_type array) : Set.t list =
  let len = Array.length dta in
  if len = 0 then [] else

  let vert = Array.init len (fun _ -> {index = -1; low = -1; onstack = false}) in
  let stack = Array.make len (-1) in
  let stack_top = ref 0 in
  let index = ref 0 in
  let sccs = ref [] in

  let rec connect x =
    stack.(!stack_top) <- x;
    incr stack_top;
    let v = vert.(x) in
    v.onstack <- true;
    v.index <- !index;
    v.low <- !index;
    incr index;
    def_type v dta.(x);
    if v.low = v.index then sccs := scc x Set.empty :: !sccs

  and scc x ys =
    decr stack_top;
    let y = stack.(!stack_top) in
    vert.(y).onstack <- false;
    let ys' = Set.add y ys in
    if x = y then ys' else scc x ys'

  and def_type v = function
    | T.StructDefType (T.StructType fts) -> List.iter (field_type v) fts
    | T.ArrayDefType (T.ArrayType ft) -> field_type v ft
    | T.FuncDefType (T.FuncType (vts1, vts2)) ->
      List.iter (value_type v) vts1; List.iter (value_type v) vts2

  and field_type v (T.FieldType (st, _)) =
    match st with
    | T.ValueStorageType vt -> value_type v vt
    | T.PackedStorageType _ -> ()

  and value_type v = function
    | T.RefType (_, ht) -> heap_type v ht
    | T.NumType _ | T.BotType -> ()

  and heap_type v = function
    | T.DefHeapType (T.SynVar x')
    | T.RttHeapType (T.SynVar x', _) ->
      let x = Int32.to_int x' in
      let w = vert.(x) in
      if w.index = -1 then begin
        connect x;
        v.low <- min v.low w.low
      end else if w.onstack then
        v.low <- min v.low w.index
    | _ -> ()
  in

  for x = 0 to len - 1 do
    if vert.(x).index = -1 then connect x
  done;
  List.rev !sccs


type def_key =
  | StructKey of field_key array
  | ArrayKey of field_key
  | FuncKey of value_key array * value_key array

and field_key =
  | ValueFieldKey of value_key * T.mutability
  | PackedFieldKey of T.pack_size

and value_key =
  | NumKey of T.num_type
  | RefKey of T.nullability * heap_key

and heap_key =
  | DefHeapKey of var_key
  | RttHeapKey of var_key * int32 option
  | OtherHeapKey of T.heap_type

and var_key =
  | ExtVarKey of int32
  | RecVarKey of int list


type def_label =
  | StructLabel of field_label array
  | ArrayLabel of field_label
  | FuncLabel of value_label array * value_label array

and field_label =
  | ValueFieldLabel of value_label * T.mutability
  | PackedFieldLabel of T.pack_size * T.mutability

and value_label =
  | NumLabel of T.num_type
  | RefLabel of T.nullability * heap_label

and heap_label =
  | DefHeapLabel of var_label
  | RttHeapLabel of var_label * int32 option
  | OtherHeapLabel of T.heap_type

and var_label =
  | RecVarLabel
  | PriorVarLabel of int32

(*
let rec def_label = function
  | T.StructDefType (T.StructType fts) ->
    StructLabel (Array.map field_label (Array.of_list fts))
  | T.ArrayDefType (T.ArrayType ft) -> ArrayLabel (field_label ft)
  | T.FuncDefType (T.FuncType (vts1, vts2)) ->
    FuncLabel (
      Array.map value_label (Array.of_list vts1),
      Array.map value_label (Array.of_list vts2)
    )

and field_label (T.FieldType (st, mut)) =
  match st with
  | T.ValueStorageType vt -> ValueFieldLabel (value_label vt, mut)
  | T.PackedStorageType sz -> PackedFieldLabel (sz, mut)

and value_label = function
  | T.NumType t -> NumLabel t
  | T.RefType (null, ht) -> RefLabel (null, heap_label ht)
  | T.BotType -> assert false

and heap_label = function
  | T.DefHeapType _ -> DefHeapLabel
  | T.RttHeapType (_, d) -> RttHeapLabel d
  | ht -> OtherHeapLabel ht
*)

let rec label r dt : (int * def_label) * int array =
  let xs = ref [] in
  let label = def_label r xs dt in
  (Hashtbl.hash label, label), Array.of_list (List.rev !xs)

and def_label r xs = function
  | T.StructDefType (T.StructType fts) ->
    StructLabel (Array.map (field_label r xs) (Array.of_list fts))
  | T.ArrayDefType (T.ArrayType ft) -> ArrayLabel (field_label r xs ft)
  | T.FuncDefType (T.FuncType (vts1, vts2)) ->
    FuncLabel (
      Array.map (value_label r xs) (Array.of_list vts1),
      Array.map (value_label r xs) (Array.of_list vts2)
    )

and field_label r xs (T.FieldType (st, mut)) =
  match st with
  | T.ValueStorageType vt -> ValueFieldLabel (value_label r xs vt, mut)
  | T.PackedStorageType sz -> PackedFieldLabel (sz, mut)

and value_label r xs = function
  | T.NumType t -> NumLabel t
  | T.RefType (null, ht) -> RefLabel (null, heap_label r xs ht)
  | T.BotType -> assert false

and heap_label r xs = function
  | T.DefHeapType x -> DefHeapLabel (var_label r xs x)
  | T.RttHeapType (x, d) -> RttHeapLabel (var_label r xs x, d)
  | ht -> OtherHeapLabel ht

and var_label r xs = function
  | T.SynVar x' ->
    let x = Int32.to_int x' in
    if Set.mem x r then (xs := x :: !xs; RecVarLabel) else PriorVarLabel x'
  | T.SemVar _ -> assert false


module Part =
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
if ex.set >= p.num then
Printf.printf "!e=%d set=%d num=%d\n%!" e  ex.set p.num;
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
    ) p.st

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

module LabelHash =
struct
  type t = int * def_label
  let equal = (=)
  let hash = fst
end
module LabelHashtbl = Hashtbl.Make(LabelHash)

module Vert =
struct
  type vert_idx = int
  type edge = {from : vert_idx; pos : int; to_ : vert_idx; mutable index : int}
  type t =
    { mutable typeidx : int;
      mutable label : int * def_label;
      mutable succs : vert_idx array;
      mutable inedges : edge list;
    }

  let make _ =
    { typeidx = -1;
      label = 0, StructLabel [||];
      succs = [||];
      inedges = [];
    }

  let compare_edge_pos {pos = pos1; _} {pos = pos2; _} = compare pos1 pos2
end

type task = {block : int; mutable first_pos : int; last_pos : int}

let partition dta sccmap scc =
  let num_verts = Set.cardinal scc in

  (* Create vertex map *)
  let verts = Array.init num_verts Vert.make in
  Set.iter (fun x ->
    let vx = verts.(sccmap.(x)) in
    let label, succs = label scc dta.(x) in
    let open Vert in
    vx.typeidx <- x;
    vx.label <- label;
    vx.succs <- succs;
    for i = 0 to Array.length succs - 1 do
      succs.(i) <- sccmap.(succs.(i))
    done
  ) scc;

  (* Initialise edge map *)
  let num_edges = ref 0 in
  let max_arity = ref (-1) in
  for v = 0 to num_verts - 1 do
    let open Vert in
    let vx = verts.(v) in
    let outarity = Array.length vx.succs in
    num_edges := !num_edges + outarity;
    max_arity := max !max_arity outarity;
    for i = 0 to outarity - 1 do
      let w = vx.succs.(i) in
      let wx = verts.(w) in
      wx.inedges <- {from = v; pos = i; to_ = w; index = -1} :: wx.inedges
    done
  done;
  let e = ref 0 in
  let edges = Array.make !num_edges
    Vert.{from = -1; pos = -1; to_ = -1; index = -1} in
  for v = 0 to num_verts - 1 do
    let open Vert in
    List.iter (fun edge ->
      edges.(!e) <- edge; edge.index <- !e; incr e
    ) verts.(v).inedges
  done;
Printf.printf "[edges:";
Array.iteri Vert.(fun i edge -> Printf.printf " %d:%d[%d]->%d" i edge.from edge.pos edge.to_) edges;
Printf.printf "]\n%!";

  (* Initialise data structures *)
  let blocks = Part.make num_verts in
  let splitters = Part.make !num_edges in

  (* Initialise blocks: partition by vertex label *)
  let labelmap = LabelHashtbl.create num_verts in
  for v = 0 to num_verts - 1 do
    let label = verts.(v).Vert.label in
    let vs = 
      match LabelHashtbl.find_opt labelmap label with
      | None -> []
      | Some vs -> vs
    in LabelHashtbl.replace labelmap label (v::vs)
  done;
  let num_blocks, l = LabelHashtbl.fold
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
(*
          let n = Array.length verts.(v).Vert.succs in
          if n > 0 then agenda := {block = s; first_pos = 0; last_pos = n} :: !agenda;
*)
          l + 1
        ) l vs
      in
      sx.last <- l';
      (s + 1, l')
    ) labelmap (0, 0)
  in
  blocks.Part.num <- num_blocks;
  assert (l = num_verts);
  Part.assert_valid blocks;

  (* Initialise splitters: partition by edge position and label *)
  let posmap = Array.make (!max_arity + 1) [] in
  for e = 0 to !num_edges - 1 do
    let pos = edges.(e).Vert.pos in
    posmap.(pos) <- e :: posmap.(pos);
  done;
  let s = ref (-1) in
  let l = ref 0 in
  let edge_block e = blocks.Part.el.(edges.(e).Vert.to_).Part.set in
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
  splitters.Part.st.(!s).Part.last <- !l;
  splitters.Part.num <- !s + 1;
  assert (!l = !num_edges);
  Part.assert_valid splitters;

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

Printf.printf "[%d verts, %d egdes, %d blocks, %d splitters]\n%!"
num_verts !num_edges blocks.Part.num splitters.Part.num;
Printf.printf "[blocks: ";
Part.print blocks;
Printf.printf ", splitters: ";
Part.print splitters;
Printf.printf "]\n%!";

  (* Main loop *)
  while !unready_splitters_top <> 0 do
    decr unready_splitters_top;
    let sp = unready_splitters.(!unready_splitters_top) in
    let e = ref (Part.set_first splitters sp) in
    while !e <> -1 do
Printf.printf "[splitter %d egde %d]\n" sp !e;
      let v = edges.(!e).Vert.from in
      let b = Part.elem_set blocks v in
      if Part.set_has_no_marks blocks b then begin
        touched_blocks.(!touched_blocks_top) <- b;
        incr touched_blocks_top
      end;
      Part.elem_mark blocks v;
Printf.printf "[blocks: ";
Part.print blocks;
Printf.printf "]\n%!";
Part.assert_valid blocks;
      e := Part.elem_next splitters !e;
Part.assert_valid blocks;
    done;
    while !touched_blocks_top <> 0 do
      decr touched_blocks_top;
      let b = touched_blocks.(!touched_blocks_top) in
      let b' = Part.set_split blocks b in
Part.assert_valid blocks;
      if b' <> -1 then begin
Printf.printf "[block %d vert %d] " b b';
Part.print blocks; Printf.printf "\n";
Part.assert_valid splitters;
        let b'' =
          if Part.set_size blocks b < Part.set_size blocks b' then b else b' in
        let v = ref (Part.set_first blocks b'') in
        while !v <> -1 do
          let vx = verts.(!v) in
          List.iter (fun edge ->
            let sp = Part.elem_set splitters edge.Vert.index in
            if Part.set_has_no_marks splitters sp then begin
              touched_splitters.(!touched_splitters_top) <- sp;
              incr touched_splitters_top
            end;
            Part.elem_mark splitters edge.Vert.index;
          ) vx.Vert.inedges;
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
  Part.assert_valid blocks;
  Part.assert_valid splitters;

(*
  (* Refinement loop *)
  while !agenda <> [] do
    let task = List.hd !agenda in
    let pos = task.first_pos in
    let pos' = pos + 1 in
    if pos' = task.last_pos then
      agenda := List.tl !agenda
    else
      task.first_pos <- pos';
    let b = task.block in
    let bx = part.pl.(b) in
    assert (bx.mid = bx.first);
    for i = bx.first to bx.last - 1 do
      let v = part.elems.(i) in
      let vx = verts.(v) in
      assert (vx.set = b);
      for j = 0 to Array.length vx.inedges - 1 do  (* quadratic? *)
        if vx.inedge.(j).pos = pos then begin
          let w = vx.inedge.(j).vert in
          let wx = part.el.(w) in
          assert (wx.loc = w);
          if wx.set = b && wx.loc >= bx.mid then begin
            (* Swap vertex to left *)
            let u = part.elems.(bx.mid) in
            let ux = part.el.(u) in
            assert (part.elems.(wx.loc) = w);
            assert (ux.loc = bx.mid);
            ux.loc <- wx.loc;
            wx.loc <- bx.mid;
            part.elems.(wx.loc) <- w;
            part.elems.(ux.loc) <- u;
            bx.mid <- bx.mid + 1
          end
        end
      done
    done
  done
*)
  blocks, splitters

let _print_agenda p agenda =
  let open Part in
  let first = ref true in
  List.iter (fun task ->
    if !first then first := false else Printf.printf " ";
    Printf.printf "%d(%d-%d)" p.elems.(task.block) task.first_pos task.last_pos
  ) !agenda

let print_sccs dts =
  let dta = Array.of_list dts in
  Gc.compact ();
  let gc_start = Gc.quick_stat () in
  let time_start = Unix.times () in
  let sccs = scc_deftypes dta in
  let sccmap = Array.make (Array.length dta) (-1) in
  List.iter (fun scc ->
    ignore (Set.fold (fun x v ->
      sccmap.(x) <- v; v + 1
    ) scc 0)
  ) sccs;
  assert (Array.for_all ((<>) (-1)) sccmap);
  let parts = List.map (partition dta sccmap) sccs in 
  let time_end = Unix.times () in
  let gc_end = Gc.quick_stat () in
  Printf.printf "Time: user %.2f ms, system %.2f ms; GC: major %d, minor %d, compactions %d\n"
    ((time_end.Unix.tms_utime -. time_start.Unix.tms_utime) /. 1000.0)
    ((time_end.Unix.tms_stime -. time_start.Unix.tms_stime) /. 1000.0)
    (gc_end.Gc.major_collections - gc_start.Gc.major_collections)
    (gc_end.Gc.minor_collections - gc_start.Gc.minor_collections)
    (gc_end.Gc.compactions - gc_start.Gc.compactions);
  Printf.printf "Recursion groups:\n";
  List.iter2 (fun xs (blocks, splitters) ->
    Printf.printf "  ";
    Set.iter (Printf.printf "%d ") xs;
    Printf.printf " (blocks: ";
    Part.print blocks;
    Printf.printf ", splitters: ";
    Part.print splitters;
    Printf.printf ")\n";
  ) sccs parts
