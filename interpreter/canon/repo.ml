(* Type Repository *)

(* Implementation based on ideas from:
 *  Laurent Mauborgne
 *  "An Incremental Unique Representation for Regular Trees"
 *  Nordic Journal of Computing, 7(2008)
 *)

type id = int
type comp_id = int
type plain_key = {label : Label.t; succs : Vert.idx array}
type partial_key =
  | NodeKey of {plain_key : plain_key; inner : partial_key array}
  | PathKey of int list

type rep =
  { comp : comp_id;  (* type's SCC's id, with all inners = [] *)
    idx : Vert.idx;  (* type's index into its SCC, -1 if not recursive *)
  }
type comp =
  { verts : Vert.t array;  (* the vertices of the component *)
    unrolled : (Label.t * int * id, unit) Hashtbl.t;
      (* occurring labels l that have pos edges to other inner vertices *)
  }


(* State *)

let dummy_rep = {comp = -1; idx = -1}
let dummy_comp = {verts = [||]; unrolled = Hashtbl.create 0}

let id_count = ref 0
let comp_count = ref 0
let id_table : rep Arraytbl.t = Arraytbl.make 33 dummy_rep
let comp_table : comp Arraytbl.t = Arraytbl.make 33 dummy_comp
let plain_table : (plain_key, id) Hashtbl.t = Hashtbl.create 33
let rec_table : (partial_key, id) Hashtbl.t = Hashtbl.create 11


(* Statistics *)

type stat =
  { mutable total_comp : int;
    mutable total_vert : int;
    mutable flat_new : int;
    mutable flat_found : int;
    mutable rec_new : int;
    mutable rec_found_pre : int;
    mutable rec_found_post : int;
    mutable rec_unrolled_pre : int;
    mutable rec_unrolled_post : int;
    mutable min_count : int;
    mutable min_comps : int;
    mutable min_verts : int;
  }

let stat =
  { total_comp = 0;
    total_vert = 0;
    flat_new = 0;
    flat_found = 0;
    rec_new = 0;
    rec_found_pre = 0;
    rec_found_post = 0;
    rec_unrolled_pre = 0;
    rec_unrolled_post = 0;
    min_count = 0;
    min_comps = 0;
    min_verts = 0;
  }

(* Statistics hack *)
type adddesc = Unknown | NonrecNew | NonrecOld | RecNew | RecOldPre | RecOldReachedPre | RecOldReached | RecOldUnreached
let adddesc : adddesc array ref = ref [||]


(* Verification *)

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
          let rep' = Arraytbl.get id_table id in
          let comp' = Arraytbl.get comp_table rep'.comp in
          assert (comp'.verts == comp);
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
  assert (!id_count <= Arraytbl.size id_table);
  assert (!comp_count <= Arraytbl.size comp_table);
  Array.iteri (fun i comp ->
    if i >= !comp_count then () else let _ = () in
    assert (Vert.assert_valid_graph !id_count comp.verts);
    Array.iter (fun vert ->
      assert (vert.Vert.inner = [||])
    ) comp.verts;
    Hashtbl.iter (fun (label, pos, id) () ->
      assert (
        Array.exists (fun vert ->
          vert.Vert.label = label && vert.Vert.succs.(pos) = id
        ) comp.verts
      )
    ) comp.unrolled
  ) !comp_table;
  Array.iteri (fun i rep ->
    if i >= !id_count then () else let _ = () in
    assert (rep.comp < !comp_count);
    let comp = Arraytbl.get comp_table rep.comp in
    assert (rep.idx >= 0 || rep.idx = -1);
    assert (rep.idx >= 0 || Array.length comp.verts = 1);
    assert (rep.idx < Array.length comp.verts);
  ) !id_table;
  Hashtbl.iter (fun k id ->
    assert (id < !id_count);
    let rep = Arraytbl.get id_table id in
    assert (rep.idx = -1);
    let comp = Arraytbl.get comp_table rep.comp in
    assert (Array.length comp.verts = 1);
    assert (comp.verts.(0).Vert.label = k.label);
    assert (comp.verts.(0).Vert.succs = k.succs);
    assert (comp.verts.(0).Vert.inner = [||]);
  ) plain_table;
  Hashtbl.iter (fun k id ->
    assert (id < !id_count);
    let rep = Arraytbl.get id_table id in
    assert (rep.idx >= 0);
    let comp = Arraytbl.get comp_table rep.comp in
    assert (assert_valid_key comp.verts 0 comp.verts.(rep.idx) true k);
  ) rec_table;
  true


(* Key computation *)

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


(* Initial graph construction *)

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


(* dta : typeidx->def_type array, as in input module
 * dtamap : typeidx->id array, mapping (known) typeidx's to id's
 * scc : typeidx set, current SCC to add
 * sccmap : typeidx->vertidx array, mapping type to relative index in their SCC
 *
 * Fills in dtamap with new mappings for nodes in scc.
 *
 * TODO: This function needs some clean-up refacting!
 *)
let add_scc dta dtamap scc sccmap =
(* Printf.printf "[add"; IntSet.iter (Printf.printf " %d") scc; Printf.printf "]%!"; *)
  assert (IntSet.for_all (fun x -> dtamap.(x) = -1) scc);
  stat.total_comp <- stat.total_comp + 1;
  stat.total_vert <- stat.total_vert + IntSet.cardinal scc;
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
        let rep = Arraytbl.get id_table id in
        (* If those are themselves recursive... *)
        if rep.idx <> -1 && not (IntMap.mem rep.comp !adj_comps) then begin
          let comp = Arraytbl.get comp_table rep.comp in
          (* And if their component contains a vertex with the same label... *)
          if Hashtbl.mem comp.unrolled (vert.label, i, id) then begin
            (* Add component and its vertices *)
            adj_comps := IntMap.add rep.comp !num_comps !adj_comps;
            incr num_comps;
            for j = 0 to Array.length comp.verts - 1 do
              assert (comp.verts.(j).id >= 0);
              adj_verts := IntMap.add comp.verts.(j).id !num_verts !adj_verts;
              incr num_verts
            done;
          end;
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
        stat.flat_found <- stat.flat_found + 1;
!adddesc.(x) <- NonrecOld;
(* Printf.printf "[plain old %d]\n%!" id; *)
        id

      | None ->
        let id = !id_count in
        vert.Vert.id <- id;
        Arraytbl.really_set comp_table !comp_count {dummy_comp with verts};
        Arraytbl.really_set id_table id {comp = !comp_count; idx = -1};
        Hashtbl.add plain_table key id;
        incr id_count;
        incr comp_count;
        stat.flat_new <- stat.flat_new + 1;
!adddesc.(x) <- NonrecNew;
(* Printf.printf "[plain new %d]\n%!" id; *)
        assert (assert_valid_state ());
        id
    in
    assert (id >= 0);
    assert (dtamap.(x) = -1);
    dtamap.(x) <- id
  end

  (* SCC is recursive (or may be via unrolling), try partial key *)
  else begin
    let k0 = partial_key verts verts.(0) in
    match Hashtbl.find_opt rec_table k0 with
    | Some id0 ->
      (* Equivalent SCC exists, parallel-traverse key to find id map *)
      stat.rec_found_pre <- stat.rec_found_pre + 1;
      let rep0 = Arraytbl.get id_table id0 in
      let comp_verts = (Arraytbl.get comp_table rep0.comp).verts in
(* Printf.printf "[found pre minimization, was vert %d/%d]\n%!" rep0.idx (Array.length comp_verts); *)
      let rec add_comp v id = function
        | PathKey _ -> ()
        | NodeKey {plain_key = {label; succs}; inner} ->
          let vert = verts.(v) in
          let rep = Arraytbl.get id_table id in
          assert ((Arraytbl.get comp_table rep.comp).verts == comp_verts);
          let repo_vert = comp_verts.(rep.idx) in
          assert (label = repo_vert.Vert.label);
          assert (label = vert.Vert.label);
          assert (succs = vert.Vert.succs);
          assert (Array.length succs = Array.length repo_vert.Vert.succs);
          assert (Array.length inner = Array.length vert.Vert.inner);
          assert (Array.length repo_vert.Vert.inner = 0);
          assert (Vert.is_raw_id verts.(v).id);
          let x = Vert.raw_id vert.id in
          assert (dtamap.(x) = -1);
          dtamap.(x) <- id;
!adddesc.(x) <- RecOldPre;
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
          done
      in add_comp 0 id0 k0

    | None ->
  (* Lookup wasn't successful, need to compare with adjacent components *)

  (* Try naive comparison with adjacent components, if they are small enough *)
  let prior_size = !num_verts - own_size in
  let no_match =
    2 lsl own_size >= prior_size ||
    begin
      let rec equal map v id =
(* Printf.printf "[equal %d/%d %d/%d]\n%!" v own_size id !id_count; *)
        assert (v >= 0 && v < own_size);
        assert (id >= 0 && id < !id_count);
(* ( *)
        match IntMap.find_opt v !map with
        | Some id' -> id = id'
        | None ->
          let vert1 = verts.(v) in
          let rep = Arraytbl.get id_table id in
          let vert2 = (Arraytbl.get comp_table rep.comp).verts.(max 0 rep.idx) in
          vert1.label = vert2.label &&
          let len = Array.length vert1.succs in
          assert (len = Array.length vert2.succs);
          let pos = ref 0 in
          let i = ref (-1) in
          let eq = ref true in
          map := IntMap.add v id !map;
          while !eq && !pos < len do
            let id1 = vert1.succs.(!pos) in
            let id2 = vert2.succs.(!pos) in
            eq := id1 = id2 ||
              id1 = -1 && (incr i; equal map vert1.inner.(!i) id2);
            incr pos
          done;
          assert (not !eq || !i + 1 = Array.length vert1.inner);
          !eq
(* ) && (Printf.printf "[equal %d/%d %d/%d succeded]\n%!" v own_size id !id_count; true) *)
(* || (Printf.printf "[equal %d/%d %d/%d failed]\n%!" v own_size id !id_count; false) *)
      in
      IntMap.exists (fun compid _ ->
        let comp_verts = (Arraytbl.get comp_table compid).verts in
        let len = Array.length comp_verts in
        let no_match = ref true in
        let i = ref 0 in
        let map = ref IntMap.empty in
        while !no_match && !i < len do
          map := IntMap.empty;
(* Printf.printf "[try comp %d type %d/%d]\n%!" compid !i len; *)
          if equal map 0 comp_verts.(!i).id then no_match := false
          else incr i
        done;
        if not !no_match then begin
          stat.rec_unrolled_pre <- stat.rec_unrolled_pre + 1;
          (* Update dtamap based on map *)
          assert (IntMap.cardinal !map = own_size);
          IntMap.iter (fun v id ->
            dtamap.(Vert.raw_id verts.(v).id) <- id;
!adddesc.(Vert.raw_id verts.(v).id) <- RecOldReachedPre;
          ) !map
(* ;Printf.printf "pre-found\n%!" *)
        end;
        !no_match
      ) !adj_comps
    end
  in
(* if not no_math then Printf.printf "[rec old reached pre"; IntSet.iter (fun x -> Printf.printf " %d" dtamap.(x)) scc; Printf.printf "]%!\n"; *)

  (* Naive comparison wasn't successful or skipped, need to minimize SCC *)
  if no_match then begin
    (* Auxiliary mappings *)
    let adj_comps_inv = Array.make !num_comps (-1) in
    let adj_verts_inv = Array.make !num_verts (-1) in
    IntMap.iter (fun comp i -> adj_comps_inv.(i) <- comp) !adj_comps;
    IntMap.iter (fun v i -> adj_verts_inv.(i) <- v) !adj_verts;

    (* Construct graph for SCC, plus possibly adjacent recursive components *)
    let combined_verts = Array.make !num_verts Vert.dummy in
    for v = 0 to own_size - 1 do
      combined_verts.(v) <- verts.(v)
    done;
    let v = ref own_size in
    for c = 0 to !num_comps - 1 do
      let comp = Arraytbl.get comp_table (adj_comps_inv.(c)) in
      for v' = 0 to Array.length comp.verts - 1 do
        combined_verts.(!v) <- comp.verts.(v'); incr v
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
    stat.min_count <- stat.min_count + 1;
    stat.min_comps <- stat.min_comps + !num_comps + 1;
    stat.min_verts <- stat.min_verts + !num_verts;
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
(* Printf.printf "[test new vertices]%!"; *)
    if blocks.Minimize.Part.num = prior_size then begin
      stat.rec_unrolled_post <- stat.rec_unrolled_post + 1;
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
        (* Equivalent SCC exists, parallel-traverse key to find id map *)
        stat.rec_found_post <- stat.rec_found_post + 1;
        let rep0 = Arraytbl.get id_table id0 in
        let comp_verts = (Arraytbl.get comp_table rep0.comp).verts in
(* Printf.printf "[found post minimization, was vert %d/%d]\n%!" rep0.idx (Array.length comp_verts); *)
        let rec add_comp v id = function
          | PathKey _ -> ()
          | NodeKey {plain_key = {label; succs}; inner} ->
            let vert = min_verts.(v) in
            let rep = Arraytbl.get id_table id in
            assert ((Arraytbl.get comp_table rep.comp).verts == comp_verts);
            let repo_vert = comp_verts.(rep.idx) in
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
        stat.rec_new <- stat.rec_new + 1;
        let id0 = !id_count in
        let compid = !comp_count in
        let unrolled = Hashtbl.create min_size in
        Arraytbl.really_set comp_table !comp_count {verts = min_verts; unrolled};
        incr comp_count;
        id_count := !id_count + min_size;
        for v = 0 to min_size - 1 do
          let vert = min_verts.(v) in
          let id = id0 + v in
          let rep = {comp = compid; idx = v} in
          let k = if v = 0 then k0 else partial_key min_verts min_verts.(v) in
          Arraytbl.really_set id_table id rep;
          Hashtbl.add rec_table k id;
          (* Remap vertex'es inner edges to new ids and add unrolled edges *)
          if vert.inner <> [||] then begin
            let i = ref 0 in  (* indexes into old vert.inner *)
            for j = 0 to Array.length vert.succs - 1 do
              let w = vert.succs.(j) in
              if w = -1 then begin
                assert (vert.inner.(!i) >= 0);
                assert (vert.inner.(!i) < min_size);
                let idj = id0 + vert.inner.(!i) in
                vert.succs.(j) <- idj;
                Hashtbl.add unrolled (vert.label, j, idj) ();
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
  end
  end;

  (* Post conditions *)
  assert (IntSet.for_all (fun x -> dtamap.(x) >= 0) scc);
  assert (assert_valid_state ())
