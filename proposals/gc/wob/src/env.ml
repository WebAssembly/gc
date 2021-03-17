open Source


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
  { vals : ('v, unit) phrase Map.t;
    typs : ('t, unit) phrase Map.t;
  }

let empty = {vals = Map.empty; typs = Map.empty}

let adjoin env1 env2 =
  { vals = Map.adjoin env1.vals env2.vals;
    typs = Map.adjoin env1.typs env2.typs;
  }

let union f g env1 env2 =
  { vals = Map.union f env1.vals env2.vals;
    typs = Map.union g env1.typs env2.typs;
  }

let disjoint_union env1 env2 =
  { vals = Map.disjoint_union env1.vals env2.vals;
    typs = Map.disjoint_union env1.typs env2.typs;
  }

let dom_val env = Map.dom env.vals
let dom_typ env = Map.dom env.typs

let extend_val env x v = {env with vals = Map.add x.it (v @@ x.at) env.vals}
let extend_typ env y t = {env with typs = Map.add y.it (t @@ y.at) env.typs}
let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env ys ts = List.fold_left2 extend_typ env ys ts

let remove_val x env = {env with vals = Map.remove x.it env.vals}
let remove_typ y env = {env with typs = Map.remove y.it env.typs}

let singleton_val x v = extend_val empty x v
let singleton_typ y t = extend_typ empty y t

let not_found x =
  Printf.printf "[find `%s` @@ %s]\n%!" x.it (string_of_region x.at);
  raise Not_found

let mem_val x env = Map.mem x.it env.vals
let mem_typ y env = Map.mem y.it env.typs
let find_val x env = try Map.find x.it env.vals with Not_found -> not_found x 
let find_typ y env = try Map.find y.it env.typs with Not_found -> not_found y
let find_opt_val x env = Map.find_opt x.it env.vals
let find_opt_typ y env = Map.find_opt y.it env.typs

let map_vals f env = {env with vals = Map.map (map_it f) env.vals}
let map_typs f env = {env with typs = Map.map (map_it f) env.typs}
let mapi_vals f env = {env with vals = Map.mapi (fun x -> map_it (f x)) env.vals}
let mapi_typs f env = {env with typs = Map.mapi (fun x -> map_it (f x)) env.typs}
let fold_vals f env a = Map.fold f env.vals a
let fold_typs f env a = Map.fold f env.typs a
let iter_vals f env = Map.iter f env.vals
let iter_typs f env = Map.iter f env.typs

let vals env = Map.bindings env.vals
let typs env = Map.bindings env.typs

let sort bs = List.sort (fun (_, st1) (_, st2) -> compare_by_region st1 st2) bs
let sorted_vals env = sort (vals env)
let sorted_typs env = sort (typs env)
