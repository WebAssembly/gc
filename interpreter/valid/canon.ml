module T = Types

module IntSet = Set.Make(Int)

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


module Label =
struct
  type t = string
  type key = t * int array

  let dummy = ""

  let bool b x = Buffer.add_uint8 b (if x then 1 else 0)
  let rec int b i =
    if 0 <= i && i < 128 then Buffer.add_uint8 b i else
    (Buffer.add_uint8 b (i land 0x7f lor 0x80); int b (i lsr 7))

  type labeling = {label : t; prior_vars : int array; rec_vars : int array}
  type context =
    { scc : IntSet.t;
      buf : Buffer.t;
      mutable prior : int list;
      mutable rec_ : int list;
    }

  let rec label scc dt : labeling =
    let c = {scc; buf = Buffer.create 32; prior = []; rec_ = []} in
    def_label c dt;
    { label = Buffer.contents c.buf;
      prior_vars = Array.of_list (List.rev c.prior);
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
      then (c.prior <- -1 :: c.prior; c.rec_ <- x :: c.rec_)
      else (c.prior <- x :: c.prior; c.rec_ <- -1 :: c.rec_)
    | T.SemVar _ -> assert false

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
    | PriorVarLabel of int32

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
      if IntSet.mem x r then (xs := x :: !xs; RecVarLabel) else PriorVarLabel x'
    | T.SemVar _ -> assert false
*)
end


module Vert =
struct
  type vert_idx = int
  type edge_idx = int
  type edge =
    { from : vert_idx;
      pos : int;
      to_ : vert_idx;
      mutable idx : edge_idx;
    }
  type t =
    { typeidx : int;
      vertidx : vert_idx;
      label : Label.t;
      priors : vert_idx array;
      succs : vert_idx array;
      mutable inedges : edge list;
    }

  let dummy =
    { typeidx = -1;
      vertidx = -1;
      label = Label.dummy;
      priors = [||];
      succs = [||];
      inedges = [];
    }

  let compare_edge_pos {pos = pos1; _} {pos = pos2; _} = compare pos1 pos2

  let label scc x v dt : t =
    let open Label in
    let c = {scc; buf = Buffer.create 32; prior = []; rec_ = []} in
    Label.def_label c dt;
    { typeidx = x;
      vertidx = v;
      label = Buffer.contents c.buf;
      priors = Array.of_list (List.rev c.prior);
      succs = Array.of_list (List.rev c.rec_);
      inedges = [];
    }
end


module Minimize =
struct
  (* Implementation based on:
   *  Antti Valmari, Petri Lehtinen.
   *  "Efficient minimization of DFAs with partial transition functions".
   *  STACS 2008
   *)

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

  let minimize (verts : Vert.t array) =
    let num_verts = Array.length verts in

    (* Initialise edge map *)
    let num_edges = ref 0 in
    let max_arity = ref (-1) in
    for v = 0 to num_verts - 1 do
      let open Vert in
      let vx = verts.(v) in
      let pos = ref 0 in
      for i = 0 to Array.length vx.succs - 1 do
        let w = vx.succs.(i) in
        if w <> -1 then begin
          let wx = verts.(w) in
          wx.inedges <- {from = v; pos = !pos; to_ = w; idx = -1} :: wx.inedges;
          incr pos
        end
      done;
      num_edges := !num_edges + !pos;
      max_arity := max !max_arity !pos;
    done;
    let e = ref 0 in
    let edges = Array.make !num_edges
      Vert.{from = -1; pos = -1; to_ = -1; idx = -1} in
    for v = 0 to num_verts - 1 do
      let open Vert in
      List.iter (fun edge ->
        edges.(!e) <- edge; edge.idx <- !e; incr e
      ) verts.(v).inedges
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
      let vx = verts.(v) in
      let key = (vx.Vert.label, vx.Vert.priors) in
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
        let v = edges.(!e).Vert.from in
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
            let vx = verts.(!v) in
            List.iter (fun edge ->
              let sp = Part.elem_set splitters edge.Vert.idx in
              if Part.set_has_no_marks splitters sp then begin
                touched_splitters.(!touched_splitters_top) <- sp;
                incr touched_splitters_top
              end;
              Part.elem_mark splitters edge.Vert.idx;
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
(*
    Part.assert_valid blocks;
    Part.assert_valid splitters;
*)

    blocks, splitters
end


module Repo =
struct
  type id = int
  type key = {label : Label.t; priors : id array; succs : Vert.vert_idx array}
  type rep =
    { id : id;
      key : key;
      vert : Vert.t;
    }

  let key_table : (key, rep) Hashtbl.t = Hashtbl.create 1001
  let id_table : (id, rep) Hashtbl.t = Hashtbl.create 1001

  module PairSet =
    Set.Make(struct type t = Vert.vert_idx * id let compare = compare end)

  let rec equal ass verts v id =
    let p = (v, id) in
    PairSet.mem p !ass ||
    let vert = verts.(v) in
    let rep = Hashtbl.find id_table id in
    vert.Vert.label = rep.key.label &&
    equal_succ (ass := PairSet.add p !ass; ass) verts vert rep.key 0

  and equal_succ ass verts vert key i =
    i = Array.length verts &&
    let v' = vert.Vert.priors.(i) in
    v' <> -1 && v' = key.priors.(i) ||
    let id' = key.succs.(i) in
    id' <> -1 && equal ass verts v' id' && equal_succ ass verts vert key (i + 1)


  let verts_of_scc dta dtamap scc sccmap : Vert.t array =
    let open Vert in
    let size = IntSet.cardinal scc in
    let verts = Array.make size Vert.dummy in
    let v = ref 0 in
    IntSet.iter (fun x ->
      sccmap.(x) <- !v;
      verts.(!v) <- Vert.label scc x !v dta.(x); incr v
    ) scc;
    for v = 0 to size - 1 do
      let vert = verts.(v) in
      for i = 0 to Array.length vert.priors - 1 do
        let x = vert.priors.(i) in
        if x <> - 1 then vert.priors.(i) <- dtamap.(x)
      done;
      for i = 0 to Array.length vert.succs - 1 do
        let x = vert.succs.(i) in
        if x <> -1 then vert.succs.(i) <- sccmap.(x)
      done
    done;
    verts


  (* dta : def_type array, as in input module
   * dtamap : id array, mapping (known) typeidx's to id's
   * scc : IntSet.t, current SCC to add
   * sccmap : vertidx array, mapping recursive vars to index in their SCC
   *)
  let add_scc dta dtamap scc sccmap =
    let size = IntSet.cardinal scc in
    let verts = verts_of_scc dta dtamap scc sccmap in
    size, verts

(*
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
*)
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


let minimize dts =
  let dta = Array.of_list dts in

let dta, dts =
if !Flags.rand >= 0 then
let dta = Fuzz.fuzz !Flags.rand in
let dts = Array.to_list dta in
dta, dts
else dta, dts
in

(* Double-check statistics *)
Printf.printf "%d types%!" (List.length dts);
Printf.printf " .%!";
let module_ = Ast.{empty_module with types = List.rev (List.fold_left (fun tys dt -> Source.(dt @@ no_region) :: tys) [] dts)} in
Printf.printf " .%!";
let wasm = Encode.encode Source.(module_ @@ no_region) in
Printf.printf " .%!";
Printf.printf " (module with %s bytes)%!" I64.(to_string_u (of_int_u (String.length wasm)));
(*
DumbTypeHash.context := dts;
let th = DumbTypeTbl.create 1001 in
List.iter (fun dt -> DumbTypeTbl.replace th dt ()) dts;
Printf.printf ", %d different" (DumbTypeTbl.length th);
*)
Printf.printf "\n%!";

  Gc.compact ();
  let gc_start = Gc.quick_stat () in
  let time_start = Unix.times () in
  let sccs0 = Scc.deftypes dta in
let sccs = if true then sccs0 else [IntSet.of_list (List.init (Array.length dta) Fun.id)] in
  let dtamap = Array.init (Array.length dta) Fun.id in
  let sccmap = Array.make (Array.length dta) (-1) in
  let parts = List.fold_left (fun parts scc ->
    Minimize.minimize (Repo.verts_of_scc dta dtamap scc sccmap) :: parts
  ) [] sccs in
  let time_end = Unix.times () in
  let gc_end = Gc.quick_stat () in
  Printf.printf "Time: user %.2f ms, system %.2f ms; GC: major %d, minor %d, compactions %d\n"
    ((time_end.Unix.tms_utime -. time_start.Unix.tms_utime) *. 1000.0)
    ((time_end.Unix.tms_stime -. time_start.Unix.tms_stime) *. 1000.0)
    (gc_end.Gc.major_collections - gc_start.Gc.major_collections)
    (gc_end.Gc.minor_collections - gc_start.Gc.minor_collections)
    (gc_end.Gc.compactions - gc_start.Gc.compactions);

let max1 = List.fold_left (fun n scc -> max n (IntSet.cardinal scc)) 0 sccs0 in
let m = List.fold_left (fun m (blocks, _) -> m + blocks.Minimize.Part.num) 0 parts in
  Printf.printf "%d types (%d recursion groups, largest %d), minimized %d types\n" (Array.length dta) (List.length sccs0) max1 m;
ignore parts
(*
  List.iter2 (fun xs (blocks, splitters) ->
    Printf.printf "  ";
    IntSet.iter (Printf.printf "%d ") xs;
    Printf.printf " (blocks: ";
    Part.print blocks;
    Printf.printf ", splitters: ";
    Part.print splitters;
    Printf.printf ")\n";
  ) sccs parts
*)
