(* Ad-hoc module for testing type canonicalization *)

module T = Types


(* Profiling *)

let time_now () =
  let gc = Gc.quick_stat () in
  let time = Unix.times () in
  gc, time

let time_start () = Gc.compact (); time_now ()
let time_end () = time_now ()

let time_diff (gc_start, time_start) (gc_end, time_end) =
  Gc.{gc_end with
    major_collections = gc_end.major_collections - gc_start.major_collections;
    minor_collections = gc_end.minor_collections - gc_start.minor_collections;
    compactions = gc_end.compactions - gc_start.compactions;
  },
  Unix.{time_end with
    tms_utime = time_end.tms_utime -. time_start.tms_utime;
    tms_stime = time_end.tms_stime -. time_start.tms_stime;
  }

let time_add (gc_start, time_start) (gc_end, time_end) =
  Gc.{gc_end with
    major_collections = gc_end.major_collections + gc_start.major_collections;
    minor_collections = gc_end.minor_collections + gc_start.minor_collections;
    compactions = gc_end.compactions + gc_start.compactions;
  },
  Unix.{time_end with
    tms_utime = time_end.tms_utime +. time_start.tms_utime;
    tms_stime = time_end.tms_stime +. time_start.tms_stime;
  }

let time_print (gc, time) =
  Printf.printf "Time: user %.2f ms, system %.2f ms; GC: major %d, minor %d, compactions %d\n"
    (time.Unix.tms_utime *. 1000.0) (time.Unix.tms_stime *. 1000.0)
    gc.Gc.major_collections gc.Gc.minor_collections gc.Gc.compactions

let time_total = let now = time_now () in ref (time_diff now now)

let time_record diff = time_total := time_add !time_total diff


(* Main runner *)

let canonicalize dts =
  let dta = Array.of_list dts in

  (* Hack for fuzzing *)
  let dta, dts =
    if !Flags.canon_random < 0 then dta, dts else begin
      if !Flags.canon_seed <> -1 then Random.init !Flags.canon_seed;
      let dta = Fuzz.fuzz !Flags.canon_random in
      let dts = Array.to_list dta in
      Printf.printf "%d types generated.%!" (Array.length dta);
      let types = List.rev (   (* carefully avoid List.map to be tail-recursive *)
        List.fold_left (fun tys dt -> Source.(dt @@ no_region) :: tys) [] dts) in
      Printf.printf ".%!";
      let module_ = Source.(Ast.{empty_module with types} @@ no_region) in

      let wasm = Encode.encode module_ in
      let bytes = I64.(to_string_u (of_int_u (String.length wasm))) in
      Printf.printf ".%!";
      Printf.printf " (module with %s bytes)\n%!" bytes;

      Printf.printf "Decoding...\n%!";
      let decode_start = time_start () in
      ignore (Decode.decode "fuzzed" wasm);
      let decode_end = time_end () in
      time_print (time_diff decode_start decode_end);

      Printf.printf "Validating...\n%!";
      let valid_start = time_start () in
      Valid.check_module module_;
      let valid_end = time_end () in
      time_print (time_diff valid_start valid_end);

      dta, dts
    end
  in

  (* Main action *)
  Printf.printf "Minimizing...\n%!";
  let time1 = time_start () in

  let size = Array.length dta in
Repo.adddesc := Array.make size Repo.Unknown;  (* Temp HACK *)
  let dtamap = Array.make size (-1) in
  if not !Flags.canon_global then begin
    let sccmap = Array.make size (-1) in
    let sccs = Scc.sccs_of_deftypes dta in
    List.iter (fun scc -> Repo.add_scc dta scc dtamap sccmap) sccs
  end else begin
    let verts = Vert.graph dta in
    assert (List.for_all Fun.id
      (List.map2 IntSet.equal (Scc.sccs_of_deftypes dta) (Scc.sccs verts)));
    let blocks, _ = Minimize.minimize verts in
    (* Hack fake repo for diagnostics below *)
    let open Minimize.Part in
    let open Repo in
    Arraytbl.really_set comp_table 0 {dummy_comp with verts};
    for v = 0 to size - 1 do
      Arraytbl.really_set id_table v {comp = 0; idx = v};
      let r = blocks.elems.(blocks.st.(blocks.el.(v).set).first) in
      dtamap.(v) <- r
    done
  end;

  let time2 = time_end () in
  time_print (time_diff time1 time2);
  time_record (time_diff time1 time2);

  (* Statistics *)
  let sccs = Scc.sccs (Vert.graph dta) in
  let funs = List.fold_left (fun n -> function T.FuncDefType _ -> n + 1 | _ -> n) 0 dts in
  let strs = List.fold_left (fun n -> function T.StructDefType _ -> n + 1 | _ -> n) 0 dts in
  let arrs = List.fold_left (fun n -> function T.ArrayDefType _ -> n + 1 | _ -> n) 0 dts in
  let maxr = List.fold_left (fun n scc -> max n (IntSet.cardinal scc)) 0 sccs in
  Printf.printf "%d types (%d funcs, %d structs, %d arrays, %d recursion groups, largest %d)\n"
    size funs strs arrs (List.length sccs) maxr;

  let set = ref IntSet.empty in
  let total = ref 0 in
  let mfuns = ref 0 in
  let mstrs = ref 0 in
  let marrs = ref 0 in
  Array.iter (fun id ->
    if IntSet.mem id !set then () else
    let rep = Arraytbl.get Repo.id_table id in
    let comp = Arraytbl.get Repo.comp_table rep.Repo.comp in
    let vert = comp.Repo.verts.(max 0 rep.Repo.idx) in
    set := IntSet.add id !set;
    incr total;
    if Label.is_func vert.Vert.label then incr mfuns
    else if Label.is_struct vert.Vert.label then incr mstrs
    else if Label.is_array vert.Vert.label then incr marrs
    else assert false
  ) dtamap;
  Printf.printf "%sminimized to %d types (%d funcs, %d structs, %d arrays)\n%!"
    (if !Flags.canon_global then "globally " else "")
    !total !mfuns !mstrs !marrs;

  if not !Flags.canon_global then begin
    let open Repo in
    Printf.printf "%d repo lookups (involving %.1f types on average)\n"
      stat.total_comp (float stat.total_vert /. float stat.total_comp);
    Printf.printf "  non-recursive: %d new, %d found\n"
      stat.flat_new stat.flat_found;
    Printf.printf "  recursive: %d new, %d found (%d pre, %d post minimization), %d unrolled (%d pre, %d post minimization)\n"
      stat.rec_new
      (stat.rec_found_pre + stat.rec_found_post)
        stat.rec_found_pre stat.rec_found_post
      (stat.rec_unrolled_pre + stat.rec_unrolled_post)
        stat.rec_unrolled_pre stat.rec_unrolled_post;
    Printf.printf "  minimizations: %d (involving %.1f groups, %.1f types on average)\n%!"
      stat.min_count
      (float stat.min_comps /. float stat.min_count)
      (float stat.min_verts /. float stat.min_count);
  end;

  (* Verification & diagnostics *)
  if !Flags.canon_verify then begin
    Printf.printf "Verifying...\n%!";
    let typetbl = DumbTypeTbl.create 1001 in
    DumbTypeTbl.Hash.context := dta;
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
          | RecOldPre -> "old cyclic type pre"
          | RecOldReachedPre -> "old cyclic type reached pre"
          | RecOldReached -> "old cyclic type reached"
          | RecOldUnreached -> "old cyclic type"
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
