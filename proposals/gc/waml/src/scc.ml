(* Implementation based on:
 *  Robert Tarjan
 *  "Depth-first search and linear graph algorithms"
 *  SIAM Journal on Computing, 1(2), 1972
 *)

module W = Wasm.Types

module IntSet = Set.Make(Int)

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
    | W.NumType _ | W.VecType _ | W.BotType -> ()

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
