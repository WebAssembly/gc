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

module Scc =
struct
  type vert =
    { mutable index : int;
      mutable low : int;
      mutable onstack : bool;
    }

  (* Tarjan's SCC algorithm *)
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
(*
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
    | ExtVarLabel of int32

  type t = def_label

  let dummy = (0, StructLabel [])

  let rec label r dt : t * int array =
    let xs = ref [] in
    let label = def_label r xs dt in
    label, Array.of_list (List.rev !xs)

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
      if IntSet.mem x r then (xs := x :: !xs; RecVarLabel) else ExtVarLabel x'
    | T.SemVar _ -> assert false
*)
end


module Vert =
struct
  type idx = int
  type t =
    { id : int;
      label : Label.t;
      succs : int array;  (* id of successor, or -1 when within own SCC *)
      inner : idx array;  (* index within own SCC for each succ id of -1 *)
    }

  let dummy =
    { id = -1;
      label = Label.dummy;
      succs = [||];
      inner = [||];
    }

  let make scc x dt : t =
    let open Label in
    let c = {scc; buf = Buffer.create 32; ext = []; rec_ = []} in
    Label.def_label c dt;
    { id = x;
      label = Buffer.contents c.buf;
      succs = Array.of_list (List.rev c.ext);
      inner = Array.of_list (List.rev c.rec_);
    }
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
  (*
        assert (p.elems.(l) = e);
  *)
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
(*
    assert (l = num_verts);
    Part.assert_valid blocks;
*)

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
(*
    assert (!l = !num_edges);
    Part.assert_valid splitters;
*)

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

(*
Printf.printf "[%d verts, %d egdes, %d blocks, %d splitters]\n%!"
num_verts !num_edges blocks.Part.num splitters.Part.num;
Printf.printf "[blocks: ";
Part.print blocks;
Printf.printf ", splitters: ";
Part.print splitters;
Printf.printf "]\n%!";
*)

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
(*
    Part.assert_valid blocks;
    Part.assert_valid splitters;
*)

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
    { comp : comp_id;  (* type's SCC id *)
      idx : Vert.idx;  (* type's index into its SCC, -1 if not recursive *)
    }

  let dummy_rep = {comp = -1; idx = -1}

  let id_count = ref 0
  let comp_count = ref 0
  let id_table : rep Table.t = Table.make 33 dummy_rep
  let comp_table : comp Table.t = Table.make 11 [||]
  let plain_table : (plain_key, id) Hashtbl.t = Hashtbl.create 33
  let rec_table : (partial_key, id) Hashtbl.t = Hashtbl.create 11

  module PairSet =
    Set.Make(struct type t = Vert.idx * id let compare = compare end)

(*
  let rec equal ass verts v id =
    let p = (v, id) in
    PairSet.mem p !ass ||
    let vert = verts.(v) in
    let rep = Table.get id_table id in
    vert.Vert.label = rep.key.label &&
    equal_succ (ass := PairSet.add p !ass; ass) verts vert rep.key 0

  and equal_succ ass verts vert key i =
    i = Array.length verts &&
    let v' = vert.Vert.succs.(i) in
    v' <> -1 && v' = key.succs.(i) ||
    let id' = key.succs.(i) in
    id' <> -1 && equal ass verts v' id' && equal_succ ass verts vert key (i + 1)
*)

  let rec partial_key verts vert = partial_key' verts IntMap.empty [] vert

  and partial_key' verts map p vert =
    match IntMap.find_opt vert.Vert.id map with
    | Some k -> k
    | None ->
      let map' = IntMap.add vert.Vert.id (PathKey p) map in
      let inner = Array.mapi (fun i v ->
        partial_key' verts map' (i::p) verts.(v)) vert.Vert.inner in
      let plain_key = {label = vert.Vert.label; succs = vert.Vert.succs} in
      NodeKey {plain_key; inner}


  let verts_of_scc dta dtamap scc sccmap : Vert.t array =
    let open Vert in
    let num_verts = IntSet.cardinal scc in
    let verts = Array.make num_verts Vert.dummy in
    let v = ref 0 in
    IntSet.iter (fun x ->
      sccmap.(x) <- !v;
      verts.(!v) <- Vert.make scc (-x) dta.(x); incr v
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


  (* dta : def_type array, as in input module
   * dtamap : id array, mapping (known) typeidx's to id's
   * scc : IntSet.t, current SCC to add
   * sccmap : vertidx array, mapping recursive vars to index in their SCC
   * result : id IntMap.t, mapping SCC typeidx's to repo id's
   *)
  let rec add_scc dta dtamap scc sccmap : id IntMap.t =
    let verts = verts_of_scc dta dtamap scc sccmap in

    (* If SCC is non-recursive, look it up in plain table *)
    if Array.length verts = 1 && verts.(0).Vert.inner = [||] then begin
      let vert = verts.(0) in
      let key = {label = vert.Vert.label; succs = vert.Vert.succs} in
      let id =
        match Hashtbl.find_opt plain_table key with
        | Some id -> id
        | None ->
          let id = !id_count in
          Table.really_set comp_table !comp_count verts;
          Table.really_set id_table id {comp = !comp_count; idx = -1};
          Hashtbl.add plain_table key id;
          incr id_count;
          incr comp_count;
          id
      in
      assert (id >= 0);
      IntMap.singleton (IntSet.choose scc) id
    end else
      add_recursive verts

  and add_recursive verts =
    (* Compute set of adjacent recursive components *)
    let open Vert in
    let own_size = Array.length verts in
    let adj_comps = ref IntMap.empty in
    let adj_verts = ref IntMap.empty in
    let num_comps = ref 0 in
    let num_verts = ref own_size in
    (* For all nodes in SCC... *)
    for v = 0 to own_size - 1 do
      let succs = verts.(v).succs in
      (* For all their external successors... *)
      for i = 0 to Array.length succs - 1 do
        let id = succs.(i) in
        if id <> -1 then begin
          let rep = Table.get id_table id in
          (* If they are themselves recursive... *)
          if rep.idx <> -1 && not (IntMap.mem rep.comp !adj_comps) then begin
            adj_comps := IntMap.add rep.comp !num_comps !adj_comps;
            incr num_comps;
            (* Add all their vertices to the current graph *)
            let comp_verts = Table.get comp_table rep.comp in
            for j = 0 to Array.length comp_verts - 1 do
              assert (comp_verts.(j).id >= 0);
              adj_verts := IntMap.add comp_verts.(j).id !num_verts !adj_verts;
              incr num_verts
            done
          end
        end
      done
    done;
    let adj_comps_inv = Array.make !num_comps (-1) in
    let adj_verts_inv = Array.make !num_verts (-1) in
    IntMap.iter (fun comp i -> adj_comps_inv.(i) <- comp) !adj_comps;
    IntMap.iter (fun v i -> adj_verts_inv.(i) <- v) !adj_verts;

    (* Construct graph for SCC + adjacent components *)
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

    (* Minimize *)
    let blocks, _ = Minimize.minimize combined_verts in

    let idmap = ref IntMap.empty in
    let prior_size = !num_verts - own_size in
    if blocks.Minimize.Part.num = prior_size then begin
      (* No new vertices => SCC already exists in repo *)
      let open Minimize.Part in
      for bl = 0 to blocks.num - 1 do
        (* Find representative from repo (must be exactly 1) *)
        let i = ref blocks.st.(bl).first in
        let r = ref (-1) in
        while !r = -1 do
          assert (!i < blocks.st.(bl).first);
          let v = blocks.elems.(!i) in
          if v >= own_size then r := v else incr i
        done;
        let id = adj_verts_inv.(!r) in
        (* Add all vertices originating from new SCC to id map *)
        for i = blocks.st.(bl).first to blocks.st.(bl).last - 1 do
          let v = blocks.elems.(i) in
          assert (v < own_size || v = !r);
          if v < own_size then idmap := IntMap.add (-verts.(v).id) id !idmap
        done
      done
    end else begin
      (* New unique vertices => SCC is either new or exists elsewhere in repo *)
      let open Minimize.Part in
      (* Extract minimized SCC *)
      let min_size = blocks.num - prior_size in
      let min_verts = Array.make min_size Vert.dummy in
      let v = ref 0 in
      for bl = 0 to blocks.num - 1 do
        let v' = blocks.elems.(blocks.st.(bl).first) in
        (* If node is from new SCC *)
        if v' < own_size then begin
          (* Use first vertex in block as representative in new SCC *)
          let vert = verts.(v') in
          for i = blocks.st.(bl).first to blocks.st.(bl).last - 1 do
            assert (blocks.elems.(i) < own_size);
            adj_verts_inv.(blocks.elems.(i)) <- !v
          done;
          min_verts.(!v) <- vert;
          incr v
        end else
          assert (set_size blocks bl = 1)
      done;
      assert (Array.for_all ((<>) (-1)) adj_verts_inv);
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
              let w' = adj_verts_inv.(w) in
              if w < own_size then
                new_inner := w' :: !new_inner
              else
                vert.succs.(j) <- w'
            end
          done;
          assert (!i = Array.length vert.inner);
          let inner = Array.of_list (List.rev !new_inner) in
          min_verts.(v) <- {vert with inner}
        end
      done;

      (* Try to find SCC elsewhere in repo *)
      let vert0 = min_verts.(0) in
      let k0 = partial_key min_verts vert0 in
      match Hashtbl.find_opt rec_table k0 with
      | Some id0 ->
        (* Equivalent SCC exists, parallel-traverse to find id map *)
        let rec add_comp vert id = function
          | PathKey _ -> ()
          | NodeKey {plain_key = {label; succs}; inner} ->
            idmap := IntMap.add (-vert.id) id !idmap;
            let rep = Table.get id_table id in
            let repo_vert = (Table.get comp_table rep.comp).(rep.idx) in
            assert (label = repo_vert.Vert.label);
            assert (label = vert.Vert.label);
            assert (succs = vert.Vert.succs);
            assert (Array.length succs = Array.length repo_vert.Vert.succs);
            assert (Array.length inner = Array.length repo_vert.Vert.inner);
            assert (Array.length inner = Array.length vert.Vert.inner);
            let i = ref 0 in
            for j = 0 to Array.length succs - 1 do
              if succs.(j) = -1 then begin
                let p = inner.(!i) in
                let v' = vert.Vert.inner.(!i) in
                let id = repo_vert.Vert.succs.(j) in
                incr i;
                add_comp min_verts.(v') id p
              end
            done
        in add_comp vert0 id0 k0

      | None ->
        (* This is a new component, enter into tables *)
        Table.really_set comp_table !comp_count min_verts;
        for v = 0 to min_size - 1 do
          let vert = min_verts.(v) in
          let rep = {comp = !comp_count; idx = v} in
          let id = !id_count + v in
          let k = if v = 0 then k0 else partial_key min_verts min_verts.(v) in
          Table.really_set id_table id rep;
          Hashtbl.add rec_table k id;
          idmap := IntMap.add (-vert.id) id !idmap;
          (* Remap remaining inner edges to new nodes *)
          if vert.inner <> [||] then begin
            let i = ref 0 in  (* indexes into old vert.inner *)
            for j = 0 to Array.length vert.succs - 1 do
              let w = vert.succs.(j) in
              if w = -1 then begin
                vert.succs.(j) <- vert.inner.(!i) + !id_count;
                incr i
              end
            done;
            assert (!i = Array.length vert.inner);
            min_verts.(v) <- {vert with inner = [||]}
          end
        done;
        incr comp_count;
        id_count := !id_count + min_size
    end;
    !idmap
end


(*** Testing Stuff ************************************************************)

module Fuzz =
struct
  let fwdedge_prob = 1

  let rec fuzz_list k fuzz x n =
    fuzz_list' fuzz x n [] ((1 + Random.int k) * Random.int k)
  and fuzz_list' fuzz x n dts = function
    | 0 -> dts
    | i -> fuzz_list' fuzz x n (fuzz x n :: dts) (i - 1)

  let rec fuzz n =
    Array.init n (fun i -> fuzz_def i n)

  and fuzz_def x n =
    match Random.int 3 with
    | 0 -> T.StructDefType (T.StructType (fuzz_list 5 fuzz_field x n))
    | 1 -> T.ArrayDefType (T.ArrayType (fuzz_field x n))
    | _ -> T.FuncDefType (T.FuncType (fuzz_list 3 fuzz_val x n, fuzz_list 2 fuzz_val x n))

  and fuzz_field x n =
    T.FieldType (fuzz_storage x n, if Random.bool () then T.Mutable else T.Immutable)

  and fuzz_storage x n =
    match Random.int 10 with
    | 0 -> T.PackedStorageType T.Pack8
    | 1 -> T.PackedStorageType T.Pack16
    | _ -> T.ValueStorageType (fuzz_val x n)

  and fuzz_val x n =
    match Random.int 15 with
    | 0 -> T.NumType T.I32Type
    | 1 -> T.NumType T.I64Type
    | 2 -> T.NumType T.F32Type
    | 3 -> T.NumType T.F64Type
    | _ -> T.RefType ((if Random.bool () then T.Nullable else T.NonNullable), fuzz_heap x n)

  and fuzz_heap x n =
    match Random.int 100 with
    | 0 -> T.AnyHeapType
    | 1 -> T.EqHeapType
    | 2 -> T.I31HeapType
    | 3 -> T.DataHeapType
    | 4 -> T.FuncHeapType
    | 5 -> T.ExternHeapType
    | 6 | 7 -> T.RttHeapType (fuzz_var x n, None)
    | 8 | 9 -> T.RttHeapType (fuzz_var x n, Some (Int32.of_int (Random.int 4)))
    | _ -> T.DefHeapType (fuzz_var x n)

  and fuzz_var x n =
    let bound = if Random.int 50 = 0 then n else x in
    T.SynVar (Int32.of_int (Random.int bound))
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
    if !Flags.canon_random >= 0 then
      let dta = Fuzz.fuzz !Flags.canon_random in
      let dts = Array.to_list dta in
      dta, dts
    else dta, dts
  in

  (* Upfront statistics *)
  Printf.printf "%d types%!" (Array.length dta);
  if !Flags.canon_random >= 0 then begin
    Printf.printf " generated .%!";
    let types = List.rev (   (* carefully avoid List.map to be tail-recursive *)
      List.fold_left (fun tys dt -> Source.(dt @@ no_region) :: tys) [] dts) in
    Printf.printf " .%!";
    let wasm = Encode.encode Source.(Ast.{empty_module with types} @@ no_region) in
    let size = I64.(to_string_u (of_int_u (String.length wasm))) in
    Printf.printf " .%!";
    Printf.printf " (module with %s bytes)%!" size
  end;
  if Array.length dta < 7001 then begin (* superslow, so only for small modules *)
    DumbTypeHash.context := dts;
    let th = DumbTypeTbl.create 1001 in
    List.iter (fun dt -> DumbTypeTbl.replace th dt ()) dts;
    Printf.printf ", %d different" (DumbTypeTbl.length th);
    let funs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.FuncDefType _ -> n + 1 | _ -> n) th 0 in
    let strs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.StructDefType _ -> n + 1 | _ -> n) th 0 in
    let arrs = DumbTypeTbl.fold (fun dt _ n -> match dt with T.ArrayDefType _ -> n + 1 | _ -> n) th 0 in
    Printf.printf " (%d funcs, %d structs, %d arrays)" funs strs arrs;
  end;
  Printf.printf "\n%!";

  (* Prepare measurements *)
  Gc.compact ();
  let gc_start = Gc.quick_stat () in
  let time_start = Unix.times () in

  (* Main action *)
  let sccs = Scc.deftypes dta in
  let dtamap = Array.init (Array.length dta) Fun.id in
  let sccmap = Array.make (Array.length dta) (-1) in
  let idmap =
    if !Flags.canon_incremental then begin
      List.fold_left (fun idmap scc ->
        let idmap' = Repo.add_scc dta dtamap scc sccmap in
        IntMap.union (fun _ _ x -> Some x) idmap idmap'
      ) IntMap.empty sccs
    end else begin
      let sccs' = [List.fold_left IntSet.union IntSet.empty sccs] in
      let parts = List.fold_left (fun parts scc ->
        let verts = Repo.verts_of_scc dta dtamap scc sccmap in
        (verts, Minimize.minimize verts) :: parts
      ) [] sccs' in
      let verts, (blocks, _) = List.hd parts in
      (* Hack fake repo for diagnostics below *)
      let open Minimize.Part in
      let open Repo in
      Table.really_set comp_table 0 verts;
      let idmap = ref IntMap.empty in
      for id = 0 to Array.length verts - 1 do
        Table.really_set id_table id {comp = 0; idx = id};
        let r = blocks.elems.(blocks.st.(blocks.el.(id).set).first) in
        idmap := IntMap.add id r !idmap
      done;
      !idmap
    end
  in

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
    (Array.length dta) funs strs arrs (List.length sccs) maxr;

  (* Construct minimized types *)
  let set = ref IntSet.empty in
  let total = ref 0 in
  let mfuns = ref 0 in
  let mstrs = ref 0 in
  let marrs = ref 0 in
  IntMap.iter (fun _ id ->
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
  ) idmap;
  Printf.printf "%s minimized to %d types (%d funcs, %d structs, %d arrays)\n%!"
    (if !Flags.canon_incremental then "incrementally" else "globally")
    !total !mfuns !mstrs !marrs
