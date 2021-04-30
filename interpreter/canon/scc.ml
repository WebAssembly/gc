(* Implementation based on:
 *  Robert Tarjan
 *  "Depth-first search and linear graph algorithms"
 *  SIAM Journal on Computing, 1(2), 1972
 *)

module T = Types

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
