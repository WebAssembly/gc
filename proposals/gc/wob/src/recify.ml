module W = Wasm.Types

module IntSet = Scc.IntSet


(* Canonical Ordering *)

let inv cmp t1 t2 = -cmp t1 t2

let compare_pair cmp1 cmp2 (t11, t12) (t21, t22) =
  match cmp1 t11 t21 with
  | 0 -> cmp2 t12 t22
  | i -> i

let compare_triple cmp1 cmp2 cmp3 (t11, t12, t13) (t21, t22, t23) =
  compare_pair cmp1 (compare_pair cmp2 cmp3) (t11, (t12, t13)) (t21, (t22, t23))

let rec compare_list cmp ts1 ts2 =
  match ts1, ts2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> +1
  | t1::ts1', t2::ts2' ->
    compare_pair cmp (compare_list cmp) (t1, ts1') (t2, ts2')

let compare_sub (tys : W.sub_type array) (su : int array) recs x1 x2 =
  let open W in

  let nullability n1 n2 = compare n1 n2 in
  let mutability m1 m2 = compare m1 m2 in

  let rec var v1 v2 y1 y2 =
    match IntSet.mem y1 recs, IntSet.mem y2 recs with
    | false, false -> compare su.(y1) su.(y2)
    | false, true -> -1
    | true, false -> +1
    | true, true ->
      match Wasm.Lib.List.(index_of y1 v1, index_of y2 v2) with
      | None, None -> sub_type (y1::v1) (y2::v2) tys.(y1) tys.(y2)
      | Some n1, Some n2 -> compare n1 n2
      | Some _, None -> -1
      | None, Some _ -> +1

  and var_type v1 v2 x1 x2 = match x1, x2 with
    | StatX x1', StatX x2' ->
      var v1 v2 (Int32.to_int x1') (Int32.to_int x2')
    | _, _ -> assert false

  and num_type v1 v2 t1 t2 = compare t1 t2

  and heap_type v1 v2 t1 t2 = match t1, t2 with
    | VarHT x1, VarHT x2 -> var_type v1 v2 x1 x2
    | _, VarHT _ -> -1
    | VarHT _, _ -> +1
    | DefHT _, _ | _, DefHT _ -> assert false
    | _, _ -> compare t1 t2

  and ref_type v1 v2 t1 t2 = compare_pair nullability (heap_type v1 v2) t1 t2

  and val_type v1 v2 t1 t2 = match t1, t2 with
    | NumT nt1, NumT nt2 -> num_type v1 v2 nt1 nt2
    | RefT rt1, RefT rt2 -> ref_type v1 v2 rt1 rt2
    | _, _ -> compare t1 t2

  and result_type v1 v2 ts1 ts2 = compare_list (val_type v1 v2) ts1 ts2

  and storage_type v1 v2 t1 t2 = match t1, t2 with
    | ValStorageT vt1, ValStorageT vt2 -> val_type v1 v2 vt1 vt2
    | _, _ -> compare t1 t2

  and field_type v1 v2 t1 t2 = match t1, t2 with
    | FieldT (mut1, st1), FieldT (mut2, st2) ->
      compare_pair mutability (storage_type v1 v2) (mut1, st1) (mut2, st2)

  and struct_type v1 v2 t1 t2 = match t1, t2 with
    | StructT fts1, StructT fts2 ->
      compare_list (field_type v1 v2) fts1 fts2

  and array_type v1 v2 t1 t2 = match t1, t2 with
    | ArrayT ft1, ArrayT ft2 -> field_type v1 v2 ft1 ft2

  and func_type v1 v2 t1 t2 = match t1, t2 with
    | FuncT (ts11, ts12), FuncT (ts21, ts22) ->
      compare_pair (result_type v1 v2) (result_type v1 v2)
        (ts11, ts12) (ts21, ts22)

  and str_type v1 v2 t1 t2 = match t1, t2 with
    | DefStructT st1, DefStructT st2 -> struct_type v1 v2 st1 st2
    | DefArrayT at1, DefArrayT at2 -> array_type v1 v2 at1 at2
    | DefFuncT ft1, DefFuncT ft2 -> func_type v1 v2 ft1 ft2
    | _, _ -> compare t1 t2

  and sub_type v1 v2 t1 t2 = match t1, t2 with
    | SubT (fin1, hts1, st1), SubT (fin2, hts2, st2) ->
      let hts1' = List.sort (inv (heap_type v1 v2)) hts1 in
      let hts2' = List.sort (inv (heap_type v1 v2)) hts2 in
      compare_triple compare (compare_list (heap_type v1 v2)) (str_type v1 v2)
        (fin1, hts1', st1) (fin2, hts2', st2)
  in
  if x1 = x2 then 0 else sub_type [x1] [x2] tys.(x1) tys.(x2)


type group =
  {mutable bwd : IntSet.t; fwd : IntSet.t; mutable ord : int list}

let compare_group (tys : W.sub_type array) su g1 g2 =
  assert (g1.ord <> []);
  assert (g2.ord <> []);
  assert (g1.fwd == g2.fwd || IntSet.disjoint g1.fwd g2.fwd);
  compare_list (compare_sub tys su (IntSet.union g1.fwd g2.fwd)) g1.ord g2.ord


(* Sort types *)

open Wasm.Source

let swap a i j =
  let x = a.(i) in a.(i) <- a.(j); a.(j) <- x

let intset s =
  Wasm.Free.Set.fold (fun x s' -> IntSet.add (Int32.to_int x) s') s IntSet.empty

let recify (sts : W.sub_type phrase list) : W.rec_type phrase list * Subst.t =
  let sta = Array.of_list sts in
  let tys = Array.map Wasm.Source.it sta in
  let sccs = Array.of_list (Scc.sccs_of_subtypes tys) in
  let n = Array.length sccs in

  let groups = Array.map (fun scc ->
      let free =
        IntSet.fold (fun x s ->
          IntSet.union s (intset Wasm.Free.((sub_type tys.(x)).types))
        ) scc IntSet.empty
      in
      {bwd = IntSet.diff free scc; fwd = scc; ord = []}
    ) sccs
  in

  let su = Array.map (fun _ -> -1) tys in
  let x' = ref 0 in

  (* Sort groups *)
  let i = ref 0 in
  let sep = ref 0 in
  while !i < n do
    (* Partition into part with empty and non-empty bwd set *)
    for j = !i to n - 1 do
      let g = groups.(j) in
      if IntSet.is_empty g.bwd then
      (
        swap groups j !sep;
        incr sep;
        (* Sort recursion group *)
        assert (g.ord = []);
        g.ord <- List.sort (compare_sub tys su g.fwd) (IntSet.elements g.fwd);

(*
        (* If group has duplicates, remap to first member *)
        let x1 = ref (List.hd g.ord) in
        let xs = ref (List.tl g.ord) in
        while !xs <> [] do
          let x2 = List.hd !xs in
          if compare_sub tys su g.fwd !x1 x2 = 0 then
            su.(x2) <- !x1
          else
            x1 := x2;
          xs := List.tl !xs
        done;
*)
      )
    done;
    assert (!sep > !i);

    (* Sort partition with empty bwd set *)
    let sub = Array.sub groups !i (!sep - !i) in
    Array.stable_sort (compare_group tys su) sub;
    Array.blit sub 0 groups !i (!sep - !i);

    (* Extend substitution *)
    Array.iter (fun g ->
      List.iter (fun x ->
        su.(x) <- ((* if su.(x) <> -1 then su.(su.(x)) else*) !x');
        incr x'
      ) g.ord;
    ) sub;

    (* Remove settled indices from remaining bwd sets *)
    let xs = Array.fold_left (fun s g -> IntSet.union s g.fwd) IntSet.empty sub in
    for j = !i to n - 1 do
      let g = groups.(j) in
      g.bwd <- IntSet.diff g.bwd xs
    done;

    (* Advance front *)
    i := !sep
  done;
  assert (!x' = Array.length tys);
  assert (Array.for_all ((<>) (-1)) su);

  (* Extract resulting substitution *)
  let subst = ref Subst.empty in
  Array.iteri (fun x x' ->
    subst := Subst.add_type !subst (Int32.of_int x) (Int32.of_int x');
  ) su;

  (* Construct def_types list *)
  let types = ref [] in
  Array.iter (fun g ->
    let sts = List.map (fun x -> tys.(x)) g.ord in
    let left = sta.(IntSet.min_elt g.fwd).at.left in
    let right = sta.(IntSet.max_elt g.fwd).at.right in
    types := (W.RecT sts @@ {left; right}) :: !types
  ) groups;

  List.rev !types, !subst
