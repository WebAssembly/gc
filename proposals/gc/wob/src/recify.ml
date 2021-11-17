module W = Wasm.Types

module IntSet = Set.Make(Int)
module IntPairSet = Set.Make(struct type t = int * int let compare = compare end)


(* Strongly Connected Components *)

(* Implementation based on:
 *  Robert Tarjan
 *  "Depth-first search and linear graph algorithms"
 *  SIAM Journal on Computing, 1(2), 1972
 *)

type vert =
  { mutable index : int;
    mutable low : int;
    mutable onstack : bool;
  }

let sccs_of_subtypes (dta : W.sub_type array) : IntSet.t list =
  let len = Array.length dta in
  if len = 0 then [] else

  let info = Array.init len (fun _ -> {index = -1; low = -1; onstack = false}) in
  let stack = Array.make len (-1) in
  let stack_top = ref 0 in
  let index = ref 0 in
  let sccs = ref [] in

  let rec connect x =
    stack.(!stack_top) <- x;
    incr stack_top;
    let v = info.(x) in
    v.onstack <- true;
    v.index <- !index;
    v.low <- !index;
    incr index;
    sub_type v dta.(x);
    if v.low = v.index then sccs := scc x IntSet.empty :: !sccs

  and scc x ys =
    decr stack_top;
    let y = stack.(!stack_top) in
    info.(y).onstack <- false;
    let ys' = IntSet.add y ys in
    if x = y then ys' else scc x ys'

  and sub_type v = function
    | W.SubType (xs, st) -> List.iter (var_type v) xs; str_type v st

  and str_type v = function
    | W.StructDefType (W.StructType fts) -> List.iter (field_type v) fts
    | W.ArrayDefType (W.ArrayType ft) -> field_type v ft
    | W.FuncDefType (W.FuncType (vts1, vts2)) ->
      List.iter (value_type v) vts1; List.iter (value_type v) vts2

  and field_type v (W.FieldType (st, _)) =
    match st with
    | W.ValueStorageType vt -> value_type v vt
    | W.PackedStorageType _ -> ()

  and value_type v = function
    | W.RefType (_, ht) -> heap_type v ht
    | W.NumType _ | W.BotType -> ()

  and heap_type v = function
    | W.DefHeapType x' | W.RttHeapType x' -> var_type v x'
    | _ -> ()

  and var_type v = function
    | W.SynVar x' ->
      let x = Int32.to_int x' in
      let w = info.(x) in
      if w.index = -1 then begin
        connect x;
        v.low <- min v.low w.low
      end else if w.onstack then
        v.low <- min v.low w.index
    | _ -> assert false
  in

  for x = 0 to len - 1 do
    if info.(x).index = -1 then connect x
  done;
  List.rev !sccs


(* Canonical Ordering *)

let inv cmp t1 t2 = -cmp t1 t2

let compare_pair cmp1 cmp2 (t11, t12) (t21, t22) =
  match cmp1 t11 t21 with
  | 0 -> cmp2 t12 t22
  | i -> i

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

  let rec syn_var v y1 y2 =
    if y1 = y2 || IntPairSet.mem (y1, y2) v then 0 else
    match IntSet.mem y1 recs, IntSet.mem y2 recs with
    | false, false -> compare su.(y1) su.(y2)
    | false, true -> -1
    | true, false -> +1
    | true, true -> sub_type (IntPairSet.add (y1, y2) v) tys.(y1) tys.(y2)

  and var_type v x1 x2 = match x1, x2 with
    | SynVar x1', SynVar x2' -> syn_var v (Int32.to_int x1') (Int32.to_int x2')
    | _, _ -> assert false

  and num_type v t1 t2 = compare t1 t2

  and heap_type v t1 t2 = match t1, t2 with
    | DefHeapType x1, DefHeapType x2
    | RttHeapType x1, RttHeapType x2 -> var_type v x1 x2
    | _, DefHeapType _ -> -1
    | DefHeapType _, _ -> +1
    | _, RttHeapType _ -> -1
    | RttHeapType _, _ -> +1
    | _, _ -> compare t1 t2

  and ref_type v t1 t2 = compare_pair nullability (heap_type v) t1 t2

  and value_type v t1 t2 = match t1, t2 with
    | NumType nt1, NumType nt2 -> num_type v nt1 nt2
    | RefType rt1, RefType rt2 -> ref_type v rt1 rt2
    | _, _ -> compare t1 t2

  and result_type v ts1 ts2 = compare_list (value_type v) ts1 ts2

  and storage_type v t1 t2 = match t1, t2 with
    | ValueStorageType vt1, ValueStorageType vt2 -> value_type v vt1 vt2
    | _, _ -> compare t1 t2

  and field_type v t1 t2 = match t1, t2 with
    | FieldType (st1, mut1), FieldType (st2, mut2) ->
      compare_pair mutability (storage_type v) (mut1, st1) (mut2, st2)

  and struct_type v t1 t2 = match t1, t2 with
    | StructType fts1, StructType fts2 -> compare_list (field_type v) fts1 fts2

  and array_type v t1 t2 = match t1, t2 with
    | ArrayType ft1, ArrayType ft2 -> field_type v ft1 ft2

  and func_type v t1 t2 = match t1, t2 with
    | FuncType (ts11, ts12), FuncType (ts21, ts22) ->
      compare_pair (result_type v) (result_type v) (ts11, ts12) (ts21, ts22)

  and str_type v t1 t2 = match t1, t2 with
    | StructDefType st1, StructDefType st2 -> struct_type v st1 st2
    | ArrayDefType at1, ArrayDefType at2 -> array_type v at1 at2
    | FuncDefType ft1, FuncDefType ft2 -> func_type v ft1 ft2
    | _, _ -> compare t1 t2

  and sub_type v t1 t2 = match t1, t2 with
    | SubType (xs1, st1), SubType (xs2, st2) ->
      let xs1' = List.sort (inv (var_type v)) xs1 in
      let xs2' = List.sort (inv (var_type v)) xs2 in
      compare_pair (compare_list (var_type v)) (str_type v)
        (xs1', st1) (xs2', st2)
  in
  if x1 = x2 then 0 else sub_type IntPairSet.empty tys.(x1) tys.(x2)


type group =
  {mutable bwd : IntSet.t; fwd : IntSet.t; is_rec : bool; mutable ord : int list}

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

let recify (sts : W.sub_type phrase list) : W.def_type phrase list * Subst.t =
  let sta = Array.of_list sts in
  let tys = Array.map Wasm.Source.it sta in
  let sccs = Array.of_list (sccs_of_subtypes tys) in
  let n = Array.length sccs in

  let groups = Array.map (fun scc ->
      let free =
        IntSet.fold (fun x s ->
          IntSet.union s (intset Wasm.Free.((sub_type tys.(x)).types))
        ) scc IntSet.empty
      in
      { bwd = IntSet.diff free scc;
        fwd = scc;
        is_rec = not (IntSet.disjoint free scc);
        ord = [];
      }
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

    (* Sort types with now empty bwd set *)
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
    if not g.is_rec then
    (
      let x = IntSet.min_elt g.fwd in
      types := (W.DefType tys.(x) @@ sta.(x).at) :: !types
    )
    else
    (
      let sts = List.map (fun x -> tys.(x)) g.ord in
      let left = sta.(IntSet.min_elt g.fwd).at.left in
      let right = sta.(IntSet.max_elt g.fwd).at.right in
      types := (W.RecDefType sts @@ {left; right}) :: !types
    );
  ) groups;

  List.rev !types, !subst
