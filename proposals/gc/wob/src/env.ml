exception Clash of string

module Set =
struct
  include Set.Make(String)

  let disjoint_add x s = if mem x s then raise (Clash x) else add x s
  let disjoint_union s1 s2 = fold disjoint_add s2 s1
end

module Map =
struct
  include Map.Make(String)

  let dom m = List.fold_left (fun s (x, _) -> Set.add x s) Set.empty (bindings m)
  let keys m = List.map fst (bindings m)
  let from_list xvs = List.fold_left (fun m (x, v) -> add x v m) empty xvs
  let from_list2 xs vs = List.fold_left2 (fun m x v -> add x v m) empty xs vs
  let adjoin m1 m2 = union (fun _ y1 y2 -> Some y2) m1 m2
  let disjoint_union m1 m2 = union (fun x _ _ -> raise (Clash x)) m1 m2
  let disjoint_add x v m = disjoint_union m (singleton x v)
end


type ('v, 't) env =
  { vals : 'v Map.t;
    typs : 't Map.t;
  }

let empty = {vals = Map.empty; typs = Map.empty}

let adjoin env1 env2 =
  { vals = Map.adjoin env1.vals env2.vals;
    typs = Map.adjoin env1.typs env2.typs;
  }

let disjoint_union env1 env2 =
  { vals = Map.disjoint_union env1.vals env2.vals;
    typs = Map.disjoint_union env1.typs env2.typs;
  }

let extend_val env x v = {env with vals = Map.add x v env.vals}
let extend_typ env y t = {env with typs = Map.add y t env.typs}

let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env ys ts = List.fold_left2 extend_typ env ys ts

let singleton_val x v = extend_val empty x v
let singleton_typ y t = extend_typ empty y t

let find_val x env = Map.find_opt x env.vals
let find_typ y env = Map.find_opt y env.typs
