module Env = Map.Make(String)

type var = string

type cls =
  { id : exn;
    name : var;
    params : var list;
    sup : typ;
    mutable def : env;
  }

and typ =
  | Var of var * typ list
  | Null
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Obj
  | Tup of typ list
  | Array of typ
  | Func of var list * typ list * typ list
  | Class of cls * typ list


(* Environments *)

let empty_env = Env.empty

let extend env x c = {env with typs = Env.add x.Source.it c env.typs}
let extend_gnd env x t = extend env x (fun _ -> t)
let extend_abs env x = extend_gnd env x (Var (x, []) @@ x.at)


(* Substitution *)

let fresh_cnts = ref empty_env

let fresh x =
  let i =
    match Env.find_opt x !fresh_cnts
    | None -> 1
    | Some i -> i + 1
  in
  fresh_env := Env.add x i fresh_cnts;
  x ^ "/" ^ string_of_int i


let rec subst s t =
  if Env.is_empty s then t else
  match t with
  | Var (x, ts) when Env.mem x s -> Env.find x s (List.map (subst s) ts)
  | Var (x, ts) -> Var (x, List.map (subst s) ts)
  | Tup ts -> Tup (List.map (subst s) ts)
  | Array t -> Array (subst s t)
  | Func (xs, ts1, ts2) ->
    let xs' = List.map (fun x -> Var (fresh x, [])) xs in
    let s' = List.fold_left2 extend_gnd s xs xs' in
    Func (xs', List.map (subst s) ts1, List.map (subst s) ts2)
  | Class (c, ts) -> Class (c, List.map (subst s) ts)


(* Equivalence and Subtyping *)

let rec eq t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Var (x1, ts1), Var (x2, ts2) -> x1 = x2 && List.for_all2 eq ts1 ts2
  | Tup ts1, Tup ts2 -> List.for_all2 eq ts1 ts2
  | Array t1', Array t2' -> eq t1' t2'
  | Func (xs1, ts11, ts12), Func (xs2, ts21, ts22) ->
    List.length x1 = List.length xs2 &&
    let xs' = List.map fresh xs1 in
    let s = List.fold_left2 extend_gnd empty_env xs xs' in
    List.for_all2 eq (List.map (subst s) ts11) (List.map (subst s) ts21) &&
    List.for_all2 eq (List.map (subst s) ts12) (List.map (subst s) ts22)
  | Class (c1, ts1), Class (c2, ts2) -> c1.id == c2.id && List.for_all2 eq ts1 ts2
  | _, _ -> t1 = t2

let rec sub t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Null, Obj _ -> true
  | Null, Array _ -> true
  | Null, Func _ -> true
  | Null, Class _ -> true
  | Tup ts1, Tup ts2 -> List.for_all2 sub ts1 ts2
  | Class (c1, ts1), Class (c2, ts2) ->
    c1.id == c2.id && List.for_all2 eq ts1 ts2 ||
    let s = List.fold_left2 extend_gnd empty_env c1.params ts1 in
    sub (subst s c1.sup) t2
  | _, _ -> eq t1 t2
