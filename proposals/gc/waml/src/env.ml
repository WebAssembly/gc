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
  let values m = List.map snd (bindings m)
  let from_list xvs = List.fold_left (fun m (x, v) -> add x v m) empty xvs
  let from_list2 xs vs = List.fold_left2 (fun m x v -> add x v m) empty xs vs
  let adjoin m1 m2 = union (fun _ y1 y2 -> Some y2) m1 m2
  let diff m1 m2 = fold (fun x _ m1' -> remove x m1') m2 m1
  let disjoint_union m1 m2 = union (fun x _ _ -> raise (Clash x)) m1 m2
  let disjoint_add x v m = disjoint_union m (singleton x v)
end


type ('v, 't, 'm, 's) env =
  { vals : ('v, unit) phrase Map.t;
    typs : ('t, unit) phrase Map.t;
    mods : ('m, unit) phrase Map.t;
    sigs : ('s, unit) phrase Map.t;
  }

let empty =
  { vals = Map.empty;
    typs = Map.empty;
    mods = Map.empty;
    sigs = Map.empty;
  }

let adjoin env1 env2 =
  { vals = Map.adjoin env1.vals env2.vals;
    typs = Map.adjoin env1.typs env2.typs;
    mods = Map.adjoin env1.mods env2.mods;
    sigs = Map.adjoin env1.sigs env2.sigs;
  }

let disjoint_union env1 env2 =
  { vals = Map.disjoint_union env1.vals env2.vals;
    typs = Map.disjoint_union env1.typs env2.typs;
    mods = Map.disjoint_union env1.mods env2.mods;
    sigs = Map.disjoint_union env1.sigs env2.sigs;
  }

let dom_val env = Map.dom env.vals
let dom_typ env = Map.dom env.typs
let dom_mod env = Map.dom env.mods
let dom_sig env = Map.dom env.sigs

let extend_val env x v = {env with vals = Map.add x.it (v @@ x.at) env.vals}
let extend_typ env y t = {env with typs = Map.add y.it (t @@ y.at) env.typs}
let extend_mod env x m = {env with mods = Map.add x.it (m @@ x.at) env.mods}
let extend_sig env y s = {env with sigs = Map.add y.it (s @@ y.at) env.sigs}
let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env ys ts = List.fold_left2 extend_typ env ys ts
let extend_mods env xs ms = List.fold_left2 extend_mod env xs ms
let extend_sigs env ys ss = List.fold_left2 extend_sig env ys ss

let remove_val x env = {env with vals = Map.remove x.it env.vals}
let remove_typ y env = {env with typs = Map.remove y.it env.typs}
let remove_mod x env = {env with mods = Map.remove x.it env.mods}
let remove_sig y env = {env with sigs = Map.remove y.it env.sigs}

let singleton_val x v = extend_val empty x v
let singleton_typ y t = extend_typ empty y t
let singleton_mod x m = extend_mod empty x m
let singleton_sig y s = extend_sig empty y s

let cardinal_vals env = Map.cardinal env.vals
let cardinal_mods env = Map.cardinal env.mods

let is_empty_vals env = Map.is_empty env.vals
let is_empty_mods env = Map.is_empty env.vals

let choose_val env = Map.choose env.vals

let not_found x =
  Printf.printf "[find `%s` @@ %s]\n%!" x.it (string_of_region x.at);
  raise Not_found

let mem_val x env = Map.mem x.it env.vals
let mem_typ y env = Map.mem y.it env.typs
let mem_mod x env = Map.mem x.it env.mods
let mem_sig y env = Map.mem y.it env.sigs

let find_val x env = try Map.find x.it env.vals with Not_found -> not_found x
let find_typ y env = try Map.find y.it env.typs with Not_found -> not_found y
let find_mod x env = try Map.find x.it env.mods with Not_found -> not_found x
let find_sig y env = try Map.find y.it env.sigs with Not_found -> not_found y
let find_opt_val x env = Map.find_opt x.it env.vals
let find_opt_typ y env = Map.find_opt y.it env.typs
let find_opt_mod x env = Map.find_opt x.it env.mods
let find_opt_sig y env = Map.find_opt y.it env.sigs

let exists_val f env = Map.exists f env.vals
let exists_typ f env = Map.exists f env.typs
let exists_mod f env = Map.exists f env.mods
let exists_sig f env = Map.exists f env.sigs

let map_vals f env = {env with vals = Map.map (map_it f) env.vals}
let map_typs f env = {env with typs = Map.map (map_it f) env.typs}
let map_mods f env = {env with mods = Map.map (map_it f) env.mods}
let map_sigs f env = {env with sigs = Map.map (map_it f) env.sigs}
let mapi_vals f env = {env with vals = Map.mapi f env.vals}
let mapi_typs f env = {env with typs = Map.mapi f env.typs}
let mapi_mods f env = {env with mods = Map.mapi f env.mods}
let mapi_sigs f env = {env with sigs = Map.mapi f env.sigs}
let fold_vals f env a = Map.fold f env.vals a
let fold_typs f env a = Map.fold f env.typs a
let fold_mods f env a = Map.fold f env.mods a
let fold_sigs f env a = Map.fold f env.sigs a
let iter_vals f env = Map.iter f env.vals
let iter_typs f env = Map.iter f env.typs
let iter_mods f env = Map.iter f env.mods
let iter_sigs f env = Map.iter f env.sigs

let vals env = Map.bindings env.vals
let typs env = Map.bindings env.typs
let mods env = Map.bindings env.mods
let sigs env = Map.bindings env.sigs

let sort bs = List.sort (fun (_, st1) (_, st2) -> compare_by_region st1 st2) bs
let sorted_vals env = sort (vals env)
let sorted_typs env = sort (typs env)
let sorted_mods env = sort (mods env)
let sorted_sigs env = sort (sigs env)
