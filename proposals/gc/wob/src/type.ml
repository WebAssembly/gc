module Env = Map.Make(String)

type var = string

type cls =
  { name : var;
    params : var list;
    mutable sup : typ;
    mutable def : typ Env.t;
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
  | Inst of cls * typ list
  | Class of cls

type con = typ list -> typ
type env = con Env.t


(* Helpers *)

let var x = Var (x, [])


(* Environments *)

let empty_env = Env.empty

let extend env x c = Env.add x c env
let extend_gnd env x t = extend env x (fun _ -> t)
let extend_abs env x = extend_gnd env x (var x)

let adjoin_env env1 env2 = Env.union (fun _ x1 x2 -> Some x2) env1 env2

let lookup env x = Env.find_opt x env


(* Classes *)

let class_cnts = ref empty_env

let class_name x =
  let i =
    match Env.find_opt x !class_cnts with
    | None -> 0
    | Some i -> i
  in
  class_cnts := Env.add x (i + 1) !class_cnts;
  if i = 0 then x else x ^ "/" ^ string_of_int i

let gen_class x xs =
  { name = class_name x;
    params = xs;
    sup = Obj;
    def = empty_env;
  }

let def_class c t =
  c.sup <- t

let eq_class c1 c2 = c1.name = c2.name


(* Substitution *)

let fresh_cnts = ref empty_env

let fresh x =
  let i =
    match Env.find_opt x !fresh_cnts with
    | None -> 1
    | Some i -> i + 1
  in
  fresh_cnts := Env.add x i !fresh_cnts;
  x ^ "-" ^ string_of_int i


let rec subst s t =
  if Env.is_empty s then t else
  match t with
  | Var (x, ts) when Env.mem x s -> Env.find x s (List.map (subst s) ts)
  | Var (x, ts) -> Var (x, List.map (subst s) ts)
  | Tup ts -> Tup (List.map (subst s) ts)
  | Array t -> Array (subst s t)
  | Func (xs, ts1, ts2) ->
    let xs' = List.map fresh xs in
    let s' = List.fold_left2 extend_gnd s xs (List.map var xs') in
    Func (xs', List.map (subst s') ts1, List.map (subst s') ts2)
  | Inst (c, ts) -> Inst (subst_cls s c, List.map (subst s) ts)
  | Class c -> Class (subst_cls s c)
  | t -> t

and subst_cls s c =
  let xs' = List.map fresh c.params in
  let s' = List.fold_left2 extend_gnd s c.params (List.map var xs') in
  { c with
    params = xs';
    sup = subst s' c.sup;
    def = Env.map (subst s') c.def;
  }


(* Equivalence and Subtyping *)

let rec eq t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Var (x1, ts1), Var (x2, ts2) -> x1 = x2 && List.for_all2 eq ts1 ts2
  | Tup ts1, Tup ts2 -> List.for_all2 eq ts1 ts2
  | Array t1', Array t2' -> eq t1' t2'
  | Func (xs1, ts11, ts12), Func (xs2, ts21, ts22) ->
    List.length xs1 = List.length xs2 &&
    let xs' = List.map fresh xs1 in
    let s1 = List.fold_left2 extend_gnd empty_env xs1 (List.map var xs') in
    let s2 = List.fold_left2 extend_gnd empty_env xs2 (List.map var xs') in
    List.for_all2 eq (List.map (subst s1) ts11) (List.map (subst s2) ts21) &&
    List.for_all2 eq (List.map (subst s1) ts12) (List.map (subst s2) ts22)
  | Inst (c1, ts1), Inst (c2, ts2) -> eq_class c1 c2 && List.for_all2 eq ts1 ts2
  | Class c1, Class c2 -> eq_class c1 c2
  | t1, t2 -> t1 = t2

let rec sub t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Null, Obj -> true
  | Null, Array _ -> true
  | Null, Func _ -> true
  | Null, Class _ -> true
  | Tup ts1, Tup ts2 -> List.for_all2 sub ts1 ts2
  | Inst (c1, ts1), Inst (c2, ts2) ->
    eq_class c1 c2 && List.for_all2 eq ts1 ts2 ||
    let s = List.fold_left2 extend_gnd empty_env c1.params ts1 in
    sub (subst s c1.sup) t2
  | t1, t2 -> eq t1 t2
