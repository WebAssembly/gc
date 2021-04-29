module T = Types


(*** Auxiliaries **************************************************************)

module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

module Table =  (* A growable array *)
struct
  type 'a t = 'a array ref
  let make n x = ref (Array.make n x)
  let get t i = (!t).(i)
  let set t i x = (!t).(i) <- x
  let size t = Array.length !t
  let grow t n x =
    let t' = Array.make (Array.length !t + n) x in
    for i = 0 to Array.length !t - 1 do
      t'.(i) <- (!t).(i)
    done;
    t := t'
  let really_set t i x =
    let n = Array.length !t in
    if i >= n then grow t n x else set t i x
end


(*** Computing SCCs ***********************************************************)

(* Implementation based on:
 *  Robert Tarjan
 *  "Depth-first search and linear graph algorithms"
 *  SIAM Journal on Computing, 1(2), 1972
 *)

module Scc =
struct
  type vert =
    { mutable index : int;
      mutable low : int;
      mutable onstack : bool;
    }

  let deftypes (dta : T.def_type array) : IntSet.t list =
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
      if v.low = v.index then sccs := scc x IntSet.empty :: !sccs

    and scc x ys =
      decr stack_top;
      let y = stack.(!stack_top) in
      vert.(y).onstack <- false;
      let ys' = IntSet.add y ys in
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
end


(*** Type Graph Representation ************************************************)

module Label =
struct
  type t = string
  type key = t * int array

  let dummy = ""
  let dummy_key = (dummy, [||])

  let bool b x = Buffer.add_uint8 b (if x then 1 else 0)
  let rec int b i =
    if 0 <= i && i < 128 then Buffer.add_uint8 b i else
    (Buffer.add_uint8 b (i land 0x7f lor 0x80); int b (i lsr 7))

  type labeling = {label : t; ext_vars : int array; rec_vars : int array}
  type context =
    { scc : IntSet.t;
      buf : Buffer.t;
      mutable ext : int list;
      mutable rec_ : int list;
    }

  let rec label scc dt : labeling =
    let c = {scc; buf = Buffer.create 32; ext = []; rec_ = []} in
    def_label c dt;
    { label = Buffer.contents c.buf;
      ext_vars = Array.of_list (List.rev c.ext);
      rec_vars = Array.of_list (List.rev c.rec_);
    }

  and def_label c = function
    | T.StructDefType (T.StructType fts) ->
      Buffer.add_uint8 c.buf 1;
      List.iter (field_label c) fts;
      Buffer.add_uint8 c.buf 0
    | T.ArrayDefType (T.ArrayType ft) ->
      Buffer.add_uint8 c.buf 2;
      field_label c ft
    | T.FuncDefType (T.FuncType (vts1, vts2)) ->
      Buffer.add_uint8 c.buf 3;
      List.iter (value_label c) vts1;
      Buffer.add_uint8 c.buf 0;
      List.iter (value_label c) vts2;
      Buffer.add_uint8 c.buf 0

  and field_label c (T.FieldType (st, mut)) =
    match st with
    | T.ValueStorageType vt ->
      value_label c vt;
      bool c.buf (mut = T.Mutable)
    | T.PackedStorageType sz ->
      Buffer.add_uint8 c.buf (0xf8 lor T.packed_size sz);
      bool c.buf (mut = T.Mutable)

  and value_label c = function
    | T.NumType t -> Buffer.add_uint8 c.buf (num_label t)
    | T.RefType (null, ht) ->
      Buffer.add_uint8 c.buf (ref_label ht);
      heap_label c ht;
      bool c.buf (null = T.Nullable)
    | T.BotType -> assert false

  and num_label = function
    | T.I32Type -> 1
    | T.I64Type -> 2
    | T.F32Type -> 3
    | T.F64Type -> 4

  and ref_label = function
    | T.AnyHeapType -> 10
    | T.EqHeapType -> 11
    | T.I31HeapType -> 12
    | T.DataHeapType -> 13
    | T.FuncHeapType -> 14
    | T.ExternHeapType -> 15
    | T.DefHeapType _ -> 16
    | T.RttHeapType _ -> 17
    | T.BotHeapType -> assert false

  and heap_label c = function
    | T.DefHeapType x -> var_label c x
    | T.RttHeapType (x, d) ->
      var_label c x; int c.buf (Int32.to_int (Option.value d ~default:(-1l)) + 1)
    | _ -> ()

  and var_label c = function
    | T.SynVar x' ->
      let x = Int32.to_int x' in
      if IntSet.mem x c.scc
      then (c.ext <- -1 :: c.ext; c.rec_ <- x :: c.rec_)
      else c.ext <- x :: c.ext
    | T.SemVar _ -> assert false

  let is_struct label = label.[0] = '\x01'
  let is_array label = label.[0] = '\x02'
  let is_func label = label.[0] = '\x03'
end


module Vert =
struct
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
end


(*** Minimization *************************************************************)

(* Implementation based on:
 *  Antti Valmari, Petri Lehtinen
 *  "Efficient minimization of DFAs with partial transition functions"
 *  Symposium on Theoretical Aspects of Computer Science (STACS), 2008
 *)

module Minimize =
struct
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
      let inner = verts.(v).Vert.inner in
      let arity = Array.length inner in
      for i = 0 to arity - 1 do
        let w = inner.(i) in
        inedges.(w) <- {from = v; pos = i; to_ = w; idx = -1} :: inedges.(w)
      done;
      num_edges := !num_edges + arity;
      max_arity := max !max_arity arity;
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
end


(*** Type Repository **********************************************************)

(* Implementation based on:
 *  Laurent Mauborgne
 *  "An Incremental Unique Representation for Regular Trees"
 *  Nordic Journal of Computing, 7(2008)
 *)

module Repo =
struct
  type id = int
  type comp_id = int
  type plain_key = {label : Label.t; succs : Vert.idx array}
  type partial_key =
    | NodeKey of {plain_key : plain_key; inner : partial_key array}
    | PathKey of int list

  type comp = Vert.t array
  type rep =
    { comp : comp_id;  (* type's SCC's id, with all inners = [] *)
      idx : Vert.idx;  (* type's index into its SCC, -1 if not recursive *)
    }

  let dummy_rep = {comp = -1; idx = -1}


  (* State *)
  let id_count = ref 0
  let comp_count = ref 0
  let id_table : rep Table.t = Table.make 33 dummy_rep
  let comp_table : comp Table.t = Table.make 33 [||]
  let plain_table : (plain_key, id) Hashtbl.t = Hashtbl.create 33
  let rec_table : (partial_key, id) Hashtbl.t = Hashtbl.create 11


  let rec assert_valid_key comp d vert vert_closed = function
    | PathKey p -> assert (List.length p < Array.length comp); true
    | NodeKey {plain_key = {label; succs}; inner} ->
      assert (label = vert.Vert.label);
      assert (Array.length succs = Array.length vert.Vert.succs);
      let vins = ref [] in
      Array.iteri (fun i id ->
        assert (id >= 0 || id = -1);
        assert (id < !id_count);
        if id = -1 then
          vins := vert.Vert.succs.(i) :: !vins
        else
          assert (id = vert.Vert.succs.(i));
      ) succs;
      let vins = Array.of_list (List.rev !vins) in
      assert (Array.length vins = Array.length inner);
      if vert_closed then
        assert (vert.Vert.inner = [||])
      else
        assert (Array.length inner = Array.length vert.Vert.inner);
      Array.iteri (fun i k ->
        let id = vins.(i) in
        let w =
          if vert_closed then begin
            assert (id >= 0);
            assert (id < !id_count);
            let rep' = Table.get id_table id in
            let comp' = Table.get comp_table rep'.comp in
            assert (comp' == comp);
            rep'.idx
          end else begin
            assert (id = -1);
            vert.Vert.inner.(i)
          end
        in
        assert (w >= 0);
        assert (w < Array.length comp);
        let vert' = comp.(w) in
        assert (d < Array.length comp);
        assert (assert_valid_key comp (d + 1) vert' vert_closed k)
      ) inner;
      true

  let assert_valid_state () =
    assert (!id_count <= Table.size id_table);
    assert (!comp_count <= Table.size comp_table);
    Array.iteri (fun i verts ->
      if i >= !comp_count then () else let _ = () in
      assert (Vert.assert_valid_graph !id_count verts);
      Array.iter (fun vert ->
        assert (vert.Vert.inner = [||])
      ) verts
    ) !comp_table;
    Array.iteri (fun i rep ->
      if i >= !id_count then () else let _ = () in
      assert (rep.comp < !comp_count);
      let verts = Table.get comp_table rep.comp in
      assert (rep.idx >= 0 || rep.idx = -1);
      assert (rep.idx >= 0 || Array.length verts = 1);
      assert (rep.idx < Array.length verts);
    ) !id_table;
    Hashtbl.iter (fun k id ->
      assert (id < !id_count);
      let rep = Table.get id_table id in
      assert (rep.idx = -1);
      let comp = Table.get comp_table rep.comp in
      assert (Array.length comp = 1);
      assert (comp.(0).Vert.label = k.label);
      assert (comp.(0).Vert.succs = k.succs);
      assert (comp.(0).Vert.inner = [||]);
    ) plain_table;
    Hashtbl.iter (fun k id ->
      assert (id < !id_count);
      let rep = Table.get id_table id in
      assert (rep.idx >= 0);
      let comp = Table.get comp_table rep.comp in
      assert (assert_valid_key comp 0 comp.(rep.idx) true k);
    ) rec_table;
    true


  let rec partial_key verts vert =
    assert (Vert.assert_valid !id_count (Array.length verts) vert);
    let k = partial_key' verts (ref IntMap.empty) [] vert in
    assert (assert_valid_key verts 0 vert false k);
    k

  and partial_key' verts map p vert =
    match IntMap.find_opt vert.Vert.id !map with
    | Some k -> k
    | None ->
      map := IntMap.add vert.Vert.id (PathKey p) !map;
      let inner = Array.mapi (fun i v ->
        partial_key' verts map (i::p) verts.(v)) vert.Vert.inner in
      let succs = Array.copy vert.Vert.succs in
      NodeKey {plain_key = {label = vert.Vert.label; succs}; inner}


  let verts_of_scc dta dtamap scc sccmap : Vert.t array =
    let open Vert in
    let num_verts = IntSet.cardinal scc in
    let verts = Array.make num_verts Vert.dummy in
    let v = ref 0 in
    IntSet.iter (fun x ->
      sccmap.(x) <- !v;
      verts.(!v) <- Vert.make scc (Vert.raw_id x) dta.(x); incr v
    ) scc;
    for v = 0 to num_verts - 1 do
      let vert = verts.(v) in
      for i = 0 to Array.length vert.succs - 1 do
        let x = vert.succs.(i) in
        if x <> - 1 then vert.succs.(i) <- dtamap.(x)
      done;
      for i = 0 to Array.length vert.inner - 1 do
        vert.inner.(i) <- sccmap.(vert.inner.(i))
      done
    done;
    verts


(* Statistics hack *)
type adddesc = Unknown | NonrecNew | NonrecOld | RecNew | RecOldReached | RecOldUnreached
let adddesc : adddesc array ref = ref [||]

  (* dta : typeidx->def_type array, as in input module
   * dtamap : typeidx->id array, mapping (known) typeidx's to id's
   * scc : typeidx set, current SCC to add
   * sccmap : typeidx->vertidx array, mapping type to relative index in their SCC
   *
   * Fills in dtamap with new mappings for nodes in scc
   *)
  let add_scc dta dtamap scc sccmap =
(* Printf.printf "[add"; IntSet.iter (Printf.printf " %d") scc; Printf.printf "]%!"; *)
    assert (IntSet.for_all (fun x -> dtamap.(x) = -1) scc);
    let verts = verts_of_scc dta dtamap scc sccmap in
    assert (Vert.assert_valid_graph !id_count verts);
    assert (assert_valid_state ());

    (* Compute set of adjacent recursive components *)
    let open Vert in
    let own_size = Array.length verts in
    let adj_comps = ref IntMap.empty in
    let adj_verts = ref IntMap.empty in
    let num_comps = ref 0 in
    let num_verts = ref own_size in
    (* For all vertices in SCC... *)
    for v = 0 to own_size - 1 do
      let vert = verts.(v) in
      let succs = vert.succs in
      (* For all their external successors... *)
      for i = 0 to Array.length succs - 1 do
        let id = succs.(i) in
        if id <> -1 then begin
          let rep = Table.get id_table id in
          (* If those are themselves recursive... *)
          if rep.idx <> -1 && not (IntMap.mem rep.comp !adj_comps) then begin
            let comp_verts = Table.get comp_table rep.comp in
            (* And if their component contains a vertex with the same label... *)
            let j = ref 0 in
            while !j < Array.length comp_verts do
              let vert' = comp_verts.(!j) in
              if vert'.label = vert.label && Array.mem id vert'.succs then begin
                (* Add that component and all its vertices to the current graph *)
                adj_comps := IntMap.add rep.comp !num_comps !adj_comps;
                incr num_comps;
                for j = 0 to Array.length comp_verts - 1 do
                  assert (comp_verts.(j).id >= 0);
                  adj_verts := IntMap.add comp_verts.(j).id !num_verts !adj_verts;
                  incr num_verts
                done;
                j := Array.length comp_verts
              end;
              incr j
            done;
          end
        end
      done
    done;

    (* If SCC is non-recursive, look it up in plain table *)
    if !num_verts = 1 && verts.(0).Vert.inner = [||] then begin
      let x = IntSet.choose scc in
      let vert = verts.(0) in
      let key = {label = vert.Vert.label; succs = vert.Vert.succs} in
      let id =
        match Hashtbl.find_opt plain_table key with
        | Some id ->
!adddesc.(x) <- NonrecOld;
(* Printf.printf "[plain old %d]\n%!" id; *)
          id

        | None ->
          let id = !id_count in
          vert.Vert.id <- id;
          Table.really_set comp_table !comp_count verts;
          Table.really_set id_table id {comp = !comp_count; idx = -1};
          Hashtbl.add plain_table key id;
          incr id_count;
          incr comp_count;
!adddesc.(x) <- NonrecNew;
(* Printf.printf "[plain new %d]\n%!" id; *)
          assert (assert_valid_state ());
          id
      in
      assert (id >= 0);
      assert (dtamap.(x) = -1);
      dtamap.(x) <- id
    end

    (* SCC is recursive (or may be), need to minimize *)
    else begin
      (* Auxiliary mappings *)
      let adj_comps_inv = Array.make !num_comps (-1) in
      let adj_verts_inv = Array.make !num_verts (-1) in
      IntMap.iter (fun comp i -> adj_comps_inv.(i) <- comp) !adj_comps;
      IntMap.iter (fun v i -> adj_verts_inv.(i) <- v) !adj_verts;

      (* Construct graph for SCC + adjacent recursive components *)
      let combined_verts = Array.make !num_verts Vert.dummy in
      for v = 0 to own_size - 1 do
        combined_verts.(v) <- verts.(v)
      done;
      let v = ref own_size in
      for comp = 0 to !num_comps - 1 do
        let verts = Table.get comp_table (adj_comps_inv.(comp)) in
        for v' = 0 to Array.length verts - 1 do
          combined_verts.(!v) <- verts.(v'); incr v
        done
      done;
      assert (!v = !num_verts);
      (* Remap internal successors as inner edges *)
      for v = 0 to !num_verts - 1 do
        let vert = combined_verts.(v) in
        let new_inner = ref [] in
        let i = ref 0 in  (* index into old vert.inner *)
        let succs = Array.map (fun id ->
          if id = -1 then begin
            assert (v < own_size);
            new_inner := vert.inner.(!i) :: !new_inner; incr i; -1
          end else
            match IntMap.find_opt id !adj_verts with
            | None -> id
            | Some w -> new_inner := w :: !new_inner; -1
        ) vert.succs in
        assert (!i = Array.length vert.inner);
        let inner = Array.of_list (List.rev !new_inner) in
        combined_verts.(v) <- {vert with succs; inner}
      done;
      assert (Vert.assert_valid_graph !id_count combined_verts);

      (* Minimize *)
(* Printf.printf "[minimize]%!"; *)
      let blocks, _ = Minimize.minimize combined_verts in
(* Printf.printf "[minimize done]%!"; *)

      (* A helper for updating SCC's entries in dtamap *)
      let update_dtamap bl id r desc =
(* Printf.printf "[update bl=%d id=%d]\n%!" bl id; *)
        let open Minimize.Part in
        for i = blocks.st.(bl).first to blocks.st.(bl).last - 1 do
          let v = blocks.elems.(i) in
          assert (v < own_size || v = r);
          if v < own_size then begin
            assert (Vert.is_raw_id verts.(v).id);
            let x = Vert.raw_id verts.(v).id in
            assert (dtamap.(x) = -1);
            dtamap.(x) <- id;
!adddesc.(x) <- desc;
          end
        done
      in

      (* If result adds no vertices to repo, then SCC already exists *)
      let prior_size = !num_verts - own_size in
(* Printf.printf "[test new vertices]%!"; *)
      if blocks.Minimize.Part.num = prior_size then begin
(* Printf.printf "[no new vertices]%!"; *)
        let open Minimize.Part in
        (* For each vertex from new SCC, find representative r from repo *)
        (* Repo is minimal, so each block contains exactly 1 representative *)
        for bl = 0 to blocks.num - 1 do
          let i = ref blocks.st.(bl).first in
          let r = ref (-1) in
          while !r = -1 do
            assert (!i < blocks.st.(bl).last);
            let v = blocks.elems.(!i) in
            if v >= own_size then r := v else incr i
          done;
          update_dtamap bl adj_verts_inv.(!r) !r RecOldReached
        done
(* ;Printf.printf "[rec old reached"; IntSet.iter (fun x -> Printf.printf " %d" dtamap.(x)) scc; Printf.printf "]%!\n"; *)
      end

      (* There are new unique vertices after minimization,
       * so SCC is either new or exists elsewhere in the repo *)
      else begin
(* Printf.printf "[extract scc]%!"; *)
        (* Extract minimized SCC *)
        let module P = Minimize.Part in
        let min_size = blocks.P.num - prior_size in
        let min_verts = Array.make min_size Vert.dummy in
        let remap_verts = adj_verts_inv in  (* reuse unsed lower part of this *)
        let v = ref 0 in
        for bl = 0 to blocks.P.num - 1 do
          let open Minimize.Part in
          let v' = blocks.elems.(blocks.st.(bl).first) in
          (* If node is from new SCC *)
          if v' < own_size then begin
            (* Use first vertex in block as representative in new SCC *)
            let vert = verts.(v') in
            (* Reuse adj_verts_inv to remap block's vertices *)
            for i = blocks.st.(bl).first to blocks.st.(bl).last - 1 do
              assert (blocks.elems.(i) < own_size);
              assert (remap_verts.(blocks.elems.(i)) = -1);
              remap_verts.(blocks.elems.(i)) <- !v
            done;
            min_verts.(!v) <- vert;
            incr v
          end else
            assert (set_size blocks bl = 1)
        done;
        assert (Array.for_all ((<>) (-1)) remap_verts);
        (* Remap inner edges *)
        for v = 0 to min_size - 1 do
          let vert = min_verts.(v) in
          if vert.inner <> [||] then begin
            let new_inner = ref [] in
            let i = ref 0 in  (* indexes into old vert.inner *)
            for j = 0 to Array.length vert.succs - 1 do
              let w = vert.succs.(j) in
              if w = -1 then begin
                let w = vert.inner.(!i) in
                incr i;
                let w' = remap_verts.(w) in
                if w < own_size then
                  new_inner := w' :: !new_inner
                else
                  vert.succs.(j) <- w'
              end
            done;
            assert (!i = Array.length vert.inner);
            let inner = Array.of_list (List.rev !new_inner) in
            min_verts.(v).inner <- inner
          end
        done;
        assert (Vert.assert_valid_graph !id_count min_verts);

        (* Try to find SCC elsewhere in repo *)
(* Printf.printf "[lookup in repo]%!"; *)
        let vert0 = min_verts.(0) in
        let k0 = partial_key min_verts vert0 in
        match Hashtbl.find_opt rec_table k0 with
        | Some id0 ->
(* Printf.printf "[found]%!"; *)
          (* Equivalent SCC exists, parallel-traverse key to find id map *)
          let rec add_comp v id = function
            | PathKey _ -> ()
            | NodeKey {plain_key = {label; succs}; inner} ->
              let vert = min_verts.(v) in
              let rep = Table.get id_table id in
              let repo_vert = (Table.get comp_table rep.comp).(rep.idx) in
              assert (label = repo_vert.Vert.label);
              assert (label = vert.Vert.label);
              assert (succs = vert.Vert.succs);
              assert (Array.length succs = Array.length repo_vert.Vert.succs);
              assert (Array.length inner = Array.length vert.Vert.inner);
              assert (Array.length repo_vert.Vert.inner = 0);
              (* Add successors *)
              let i = ref 0 in
              for j = 0 to Array.length succs - 1 do
                if succs.(j) = -1 then begin
                  let p = inner.(!i) in
                  let v' = vert.Vert.inner.(!i) in
                  let id = repo_vert.Vert.succs.(j) in
                  incr i;
                  add_comp v' id p
                end
              done;
              assert (Vert.is_raw_id vert.id);
              let orig_v = sccmap.(Vert.raw_id vert.id) in
              update_dtamap blocks.P.el.(orig_v).P.set id (-1) RecOldUnreached
          in add_comp 0 id0 k0
(* ;Printf.printf "[rec old(%d) unreached" min_size; IntSet.iter (fun x -> Printf.printf " %d" dtamap.(x)) scc; Printf.printf "]%!\n"; *)

        | None ->
(* Printf.printf "[not found]%!"; *)
          (* This is a new component, enter into tables *)
          let id0 = !id_count in
          let compid = !comp_count in
          Table.really_set comp_table !comp_count min_verts;
          incr comp_count;
          id_count := !id_count + min_size;
          for v = 0 to min_size - 1 do
            let vert = min_verts.(v) in
            let id = id0 + v in
            let rep = {comp = compid; idx = v} in
            let k = if v = 0 then k0 else partial_key min_verts min_verts.(v) in
            Table.really_set id_table id rep;
            Hashtbl.add rec_table k id;
            (* Remap vertex'es inner edges to new ids *)
            if vert.inner <> [||] then begin
              let i = ref 0 in  (* indexes into old vert.inner *)
              for j = 0 to Array.length vert.succs - 1 do
                let w = vert.succs.(j) in
                if w = -1 then begin
                  assert (vert.inner.(!i) >= 0);
                  assert (vert.inner.(!i) < min_size);
                  vert.succs.(j) <- id0 + vert.inner.(!i);
                  incr i
                end
              done;
              assert (!i = Array.length vert.inner);
              min_verts.(v).inner <- [||]
            end;
            assert (Vert.is_raw_id vert.id);
            let orig_v = sccmap.(Vert.raw_id vert.id) in
            update_dtamap blocks.P.el.(orig_v).P.set id (-1) RecNew;
            vert.id <- id
          done
(* ;Printf.printf "[rec new(%d)" min_size; IntSet.iter (fun x -> Printf.printf " %d" dtamap.(x)) scc; Printf.printf "]%!\n"; *)
      end
    end;

    (* Post conditions *)
    assert (IntSet.for_all (fun x -> dtamap.(x) >= 0) scc);
    assert (assert_valid_state ())
end


(*** Testing Stuff ************************************************************)

module Fuzz =
struct
  let rec fuzz_list k fuzz x y =
    fuzz_list' fuzz x y [] ((1 + Random.int k) * Random.int k)
  and fuzz_list' fuzz x y dts = function
    | 0 -> dts
    | i -> fuzz_list' fuzz x y (fuzz x y :: dts) (i - 1)

  let rec fuzz n =
    let y = ref 0 in
    Array.init n (fun x ->
      if !y < x && Random.int 5 = 0 then
        y := x + (1 + Random.int 10) * Random.int 20 + 1;
      fuzz_def x (min n (max x !y))
    )

  and fuzz_def x y =
    match Random.int 3 with
    | 0 -> T.StructDefType (T.StructType (fuzz_list 5 fuzz_field x y))
    | 1 -> T.ArrayDefType (T.ArrayType (fuzz_field x y))
    | _ -> T.FuncDefType (T.FuncType
        (fuzz_list 3 fuzz_val x y, fuzz_list 2 fuzz_val x y))

  and fuzz_field x y =
    T.FieldType (fuzz_storage x y,
      if Random.bool () then T.Mutable else T.Immutable)

  and fuzz_storage x y =
    match Random.int 10 with
    | 0 -> T.PackedStorageType T.Pack8
    | 1 -> T.PackedStorageType T.Pack16
    | _ -> T.ValueStorageType (fuzz_val x y)

  and fuzz_val x y =
    match Random.int 15 with
    | 0 -> T.NumType T.I32Type
    | 1 -> T.NumType T.I64Type
    | 2 -> T.NumType T.F32Type
    | 3 -> T.NumType T.F64Type
    | _ -> T.RefType
        ((if Random.bool () then T.Nullable else T.NonNullable), fuzz_heap x y)

  and fuzz_heap x y =
    match Random.int 100 with
    | 0 -> T.AnyHeapType
    | 1 -> T.EqHeapType
    | 2 -> T.I31HeapType
    | 3 -> T.DataHeapType
    | 4 -> T.FuncHeapType
    | 5 -> T.ExternHeapType
    | 6 | 7 -> T.RttHeapType (fuzz_var x y, None)
    | 8 | 9 -> T.RttHeapType (fuzz_var x y, Some (Int32.of_int (Random.int 4)))
    | _ -> T.DefHeapType (fuzz_var x y)

  and fuzz_var x y =
    let idx = Random.(if bool () || x = y then int x else x + int (y - x)) in
    T.SynVar (Int32.of_int idx)
end


module DumbTypeHash =  (* just for assertions *)
struct
  type t = T.def_type

  let context : Match.context ref = ref []

  let equal dt1 dt2 = Match.eq_def_type !context [] dt1 dt2

  let rec hash_list hash = function
    | [] -> 0
    | x::xs -> hash x lxor (hash_list hash xs lsl 1)

  let rec hash = function
    | T.StructDefType (T.StructType fts) -> 1 + hash_list hash_field fts
    | T.ArrayDefType (T.ArrayType ft) -> 2 + hash_field ft
    | T.FuncDefType (T.FuncType (ts1, ts2)) ->
      3 + hash_list hash_val ts1 lxor hash_list hash_val ts2

  and hash_field (T.FieldType (st, _)) = hash_storage st

  and hash_storage = function
    | T.ValueStorageType t -> hash_val t
    | T.PackedStorageType sz -> T.packed_size sz

  and hash_val = function
    | T.NumType t -> Hashtbl.hash t
    | T.RefType (_, ht) -> hash_heap ht
    | T.BotType -> assert false

  and hash_heap = function
    | T.DefHeapType _ -> 37
    | T.RttHeapType _ -> 62
    | ht -> Hashtbl.hash ht
end

module DumbTypeTbl = Hashtbl.Make(DumbTypeHash)


let minimize dts =
  let dta = Array.of_list dts in

  (* Hack for fuzzing *)
  let dta, dts =
    if !Flags.canon_random < 0 then dta, dts else begin
      let dta = Fuzz.fuzz !Flags.canon_random in
      let dts = Array.to_list dta in
      Printf.printf "%d types generated .%!" (Array.length dta);
      let types = List.rev (   (* carefully avoid List.map to be tail-recursive *)
        List.fold_left (fun tys dt -> Source.(dt @@ no_region) :: tys) [] dts) in
      Printf.printf " .%!";
      let module_ = Source.(Ast.{empty_module with types} @@ no_region) in
      (* Printf.printf "Encoding...\n%!"; *)
      let wasm = Encode.encode module_ in
      (* Printf.printf "Validating...\n%!"; *)
      Valid.check_module module_;
      let bytes = I64.(to_string_u (of_int_u (String.length wasm))) in
      Printf.printf " .%!";
      Printf.printf " (module with %s bytes)\n%!" bytes;
      dta, dts
    end
  in

  (* Prepare measurements *)
  Printf.printf "Minimizing...\n%!";
  Gc.compact ();
  let gc_start = Gc.quick_stat () in
  let time_start = Unix.times () in

  (* Main action *)
  let size = Array.length dta in
Repo.adddesc := Array.make size Repo.Unknown;
  let dtamap = Array.make size (-1) in
  let sccmap = Array.make size (-1) in
  let sccs = Scc.deftypes dta in
  if !Flags.canon_incremental then begin
    List.iter (fun scc -> Repo.add_scc dta dtamap scc sccmap) sccs
  end else begin
    let comp = List.fold_left IntSet.union IntSet.empty sccs in
    let verts = Repo.verts_of_scc dta dtamap comp sccmap in
    assert (Array.length verts = size);
    let blocks, _ = Minimize.minimize verts in
    (* Hack fake repo for diagnostics below *)
    let open Minimize.Part in
    let open Repo in
    Table.really_set comp_table 0 verts;
    for v = 0 to size - 1 do
      Table.really_set id_table v {comp = 0; idx = v};
      let r = blocks.elems.(blocks.st.(blocks.el.(v).set).first) in
      dtamap.(v) <- r
    done;
  end;

  (* Output measurements *)
  let time_end = Unix.times () in
  let gc_end = Gc.quick_stat () in
  Printf.printf "Time: user %.2f ms, system %.2f ms; GC: major %d, minor %d, compactions %d\n"
    ((time_end.Unix.tms_utime -. time_start.Unix.tms_utime) *. 1000.0)
    ((time_end.Unix.tms_stime -. time_start.Unix.tms_stime) *. 1000.0)
    (gc_end.Gc.major_collections - gc_start.Gc.major_collections)
    (gc_end.Gc.minor_collections - gc_start.Gc.minor_collections)
    (gc_end.Gc.compactions - gc_start.Gc.compactions);

  let funs = List.fold_left (fun n -> function T.FuncDefType _ -> n + 1 | _ -> n) 0 dts in
  let strs = List.fold_left (fun n -> function T.StructDefType _ -> n + 1 | _ -> n) 0 dts in
  let arrs = List.fold_left (fun n -> function T.ArrayDefType _ -> n + 1 | _ -> n) 0 dts in
  let maxr = List.fold_left (fun n scc -> max n (IntSet.cardinal scc)) 0 sccs in
  Printf.printf "%d types (%d funcs, %d structs, %d arrays, %d recursion groups, largest %d)\n"
    size funs strs arrs (List.length sccs) maxr;

  (* Statistics *)
  let set = ref IntSet.empty in
  let total = ref 0 in
  let mfuns = ref 0 in
  let mstrs = ref 0 in
  let marrs = ref 0 in
  Array.iter (fun id ->
    if IntSet.mem id !set then () else
    let rep = Table.get Repo.id_table id in
    let comp = Table.get Repo.comp_table rep.Repo.comp in
    let vert = comp.(max 0 rep.Repo.idx) in
    set := IntSet.add id !set;
    incr total;
    if Label.is_func vert.Vert.label then incr mfuns
    else if Label.is_struct vert.Vert.label then incr mstrs
    else if Label.is_array vert.Vert.label then incr marrs
    else assert false
  ) dtamap;
  Printf.printf "%s minimized to %d types (%d funcs, %d structs, %d arrays)\n%!"
    (if !Flags.canon_incremental then "incrementally" else "globally")
    !total !mfuns !mstrs !marrs;

  (* Verification & diagnostics *)
  if !Flags.canon_verify then begin
    Printf.printf "Verifying...\n%!";
    let typetbl = DumbTypeTbl.create 1001 in
    DumbTypeHash.context := dts;
    let i = ref 0 in
    List.iteri (fun x dt ->
      let xs =
        match DumbTypeTbl.find_opt typetbl dt with
        | None -> [(x, !i)]
        | Some xs -> (x, !i)::xs
      in DumbTypeTbl.replace typetbl dt xs; incr i
    ) dts;
    let maxmult = DumbTypeTbl.fold (fun _ xs n -> max (List.length xs) n) typetbl 0 in
    Printf.printf "%d types, %d different" size (DumbTypeTbl.length typetbl);
    let funs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.FuncDefType _ -> n + 1 | _ -> n) typetbl 0 in
    let strs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.StructDefType _ -> n + 1 | _ -> n) typetbl 0 in
    let arrs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.ArrayDefType _ -> n + 1 | _ -> n) typetbl 0 in
    Printf.printf " (%d funcs, %d structs, %d arrays, max redundancy %d)\n"
      funs strs arrs maxmult;

    if true || !total <> DumbTypeTbl.length typetbl && DumbTypeTbl.length typetbl > 0
    then begin
      let dtamap_inv = ref IntMap.empty in
      Array.iteri (fun x id ->
        dtamap_inv := IntMap.update id
          (function None -> Some [x] | Some xs -> Some (x::xs)) !dtamap_inv
      ) dtamap;

      (* Compare redundancy groups as a whole *)
      let module IntListMap =
        Map.Make(struct type t = int list let compare = compare end) in
      let expdups = ref IntListMap.empty in
      let actdups = ref IntListMap.empty in
      DumbTypeTbl.iter (fun _ xs ->
        match xs with
        | [_] -> ()
        | xis ->
          let sorted = List.sort compare xis in
          expdups :=
            IntListMap.add (List.map fst sorted) (List.map snd sorted) !expdups
      ) typetbl;
      IntMap.iter (fun _ xs ->
        match xs with
        | [_] -> ()
        | xs -> actdups := IntListMap.add (List.sort compare xs) () !actdups
      ) !dtamap_inv;
      Printf.printf "%d redundancy groups expected, %d found"
        (IntListMap.cardinal !expdups) (IntListMap.cardinal !actdups);
      if IntListMap.cardinal !expdups = IntListMap.cardinal !actdups then begin
        let exps = List.map fst (IntListMap.bindings !expdups) in
        let acts = List.map fst (IntListMap.bindings !actdups) in
        let diff = ref 0 in
        List.iter2 (fun xs1 xs2 ->
          if xs1 <> xs2 then incr diff;
        ) exps acts;
        Printf.printf ", %d differ" !diff
      end;
      Printf.printf "\n";

      (* Compare membership in redundancy groups *)
      let grpsize = Array.make size (-1) in
      let expred = Array.make size [] in
      let actred = Array.make size [] in
      List.iter (fun scc ->
        let n = IntSet.cardinal scc in
        IntSet.iter (fun x -> assert (grpsize.(x) = -1); grpsize.(x) <- n) scc
      ) sccs;
      DumbTypeTbl.iter (fun _ xis ->
        List.iter (fun (x, _) -> expred.(x) <- List.map fst xis) xis
      ) typetbl;
      IntMap.iter (fun _ xs ->
        List.iter (fun x -> actred.(x) <- xs) xs
      ) !dtamap_inv;
      let diffs_by_idx = ref IntMap.empty in
      let diffs_by_id = ref IntMap.empty in
      for x = 0 to size - 1 do
        if expred.(x) <> actred.(x) then begin
          diffs_by_idx := IntMap.add x dtamap.(x) !diffs_by_idx;
          diffs_by_id := IntMap.add dtamap.(x) x !diffs_by_id;
        end
      done;
      let hasdiff = ref false in
      IntMap.iter (fun id x ->
        hasdiff := true;
        let list xs = String.concat ", " (List.map string_of_int (List.rev xs)) in
        Printf.printf "redundancy differs for type %d = #%d (expected %d [%s], got %d [%s], recursive group size %d, was added as %s)\n"
          x id
          (List.length expred.(x)) (list expred.(x))
          (List.length actred.(x)) (list actred.(x))
          grpsize.(x)
          Repo.(match !adddesc.(x) with
          | NonrecNew -> "new plain type"
          | NonrecOld -> "dup plain type"
          | RecNew -> "new cyclic type"
          | RecOldUnreached -> "old cyclic type"
          | RecOldReached -> "old cyclic type reached"
          | Unknown -> assert false
          )
      ) !diffs_by_id;

      if !hasdiff then begin
        let id, first_fail_new = IntMap.min_binding !diffs_by_id in
        let id', first_fail_old = IntMap.fold (fun id' x res ->
            if fst res <> -1 || id' = id then res else
            if List.mem x expred.(first_fail_new) then (id', x) else
            res
          ) !diffs_by_id (-1, -1) in
        Printf.printf "first failure: new %d = #%d not found for %d = #%d\n"
          first_fail_new id first_fail_old id'
      end
    end;

    Printf.printf "%!"
  end
