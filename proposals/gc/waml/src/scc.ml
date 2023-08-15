(* Strongly Connected Components *)

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
    | W.SubT (_, xs, st) -> List.iter (heap_type v) xs; str_type v st

  and str_type v = function
    | W.DefStructT (W.StructT fts) -> List.iter (field_type v) fts
    | W.DefArrayT (W.ArrayT ft) -> field_type v ft
    | W.DefFuncT (W.FuncT (vts1, vts2)) ->
      List.iter (val_type v) vts1; List.iter (val_type v) vts2

  and field_type v (W.FieldT (_, st)) =
    match st with
    | W.ValStorageT vt -> val_type v vt
    | W.PackStorageT _ -> ()

  and val_type v = function
    | W.RefT (_, ht) -> heap_type v ht
    | W.NumT _ | W.VecT _ | W.BotT -> ()

  and heap_type v = function
    | W.VarHT (W.StatX x') -> var_type v x'
    | _ -> ()

  and var_type v x' =
    let x = Int32.to_int x' in
    let w = info.(x) in
    if w.index = -1 then begin
      connect x;
      v.low <- min v.low w.low
    end else if w.onstack then
      v.low <- min v.low w.index
  in

  for x = 0 to len - 1 do
    if info.(x).index = -1 then connect x
  done;
  List.rev !sccs
