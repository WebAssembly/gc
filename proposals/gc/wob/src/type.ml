(* Types *)

type var = string
type kind = int
type mut = Mut | Const
type sort = LetS | VarS | FuncS | ClassS | ProhibitedS

type typ =
  | Var of var * typ list
  | Bot
  | Null
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Obj
  | Boxed
  | Box of typ
  | Tup of typ list
  | Array of typ * mut
  | Func of var list * typ list * typ
  | Inst of cls * typ list
  | Class of cls

and cls =
  { name : var;
    id : int;
    tparams : var list;
    mutable vparams : typ list;
    mutable sup : typ;
    mutable def : (var * (sort * typ)) list;
  }


(* Constructors and accessors *)

let var y = Var (y, [])

let is_var = function Var _ -> true | _ -> false
let is_inst = function Inst _ -> true | _ -> false

let as_tup = function Tup ts -> ts | _ -> assert false
let as_array = function Array (t, m) -> t, m | _ -> assert false
let as_func = function Func (ys, ts1, t2) -> ys, ts1, t2 | _ -> assert false
let as_inst = function Inst (c, ts) -> c, ts | _ -> assert false
let as_class = function Class c -> c | _ -> assert false


(* Printing *)

let list f xs = String.concat ", " (List.map f xs)

let rec to_string = function
  | Var (y, []) -> y
  | Var (y, ts) -> y ^ "<" ^ list to_string ts ^ ">"
  | Bot -> "Bot"
  | Null -> "Null"
  | Bool -> "Bool"
  | Byte -> "Byte"
  | Int -> "Int"
  | Float -> "Float"
  | Text -> "Text"
  | Obj -> "Object"
  | Boxed -> "Boxed"
  | Box t -> to_string t ^ "$"
  | Tup ts -> "(" ^ list to_string ts ^ ")"
  | Array (t, Mut) -> to_string t ^ "[]"
  | Array (t, Const) -> to_string t ^ "![]"
  | Func ([], ts1, t2) -> params ts1 ^ " -> " ^ to_string t2
  | Func (ys, ts1, t2) ->
    "<" ^ list Fun.id ys ^ ">(" ^ params ts1 ^ ") -> " ^ to_string t2
  | Inst (c, ts) -> to_string (Var (c.name, ts))
  | Class c -> "class " ^ c.name ^ "/" ^ string_of_int c.id

and params = function
  | [t] -> to_string t
  | ts -> "(" ^ list to_string ts ^ ")"


(* Free variables *)

module Set = Env.Set
let (++) = Set.union

let list f ts = List.fold_left (++) Set.empty (List.map f ts)

let rec free = function
  | Var (y, ts) -> Set.singleton y ++ list free ts
  | Bot | Null | Bool | Byte | Int | Float | Text | Obj | Boxed -> Set.empty
  | Tup ts -> list free ts
  | Box t | Array (t, _) -> free t
  | Func (ys, ts1, t2) -> Set.diff (list free ts1 ++ free t2) (Set.of_list ys)
  | Inst (c, ts) -> Set.singleton c.name ++ list free ts
  | Class c ->
    Set.singleton c.name ++
    Set.diff (list free c.vparams ++ free c.sup) (Set.of_list c.tparams)


(* Substitutions *)

module Subst = Env.Map

type con = typ list -> typ
type subst = con Subst.t

let empty_subst = Subst.empty
let adjoin_subst s1 s2 = Subst.union (fun _ y1 y2 -> Some y2) s1 s2

let lookup_subst s y = Subst.find_opt y s
let extend_subst s y c = Subst.add y c s
let extend_subst_typ s y t = extend_subst s y (fun _ -> t)
let extend_subst_abs s y = extend_subst_typ s y (var y)

let typ_subst ys ts = List.fold_left2 extend_subst_typ empty_subst ys ts


let fresh_cnts = ref Env.Map.empty

let fresh y =
  let i =
    match Env.Map.find_opt y !fresh_cnts with
    | None -> 1
    | Some i -> i + 1
  in
  fresh_cnts := Env.Map.add y i !fresh_cnts;
  y ^ "-" ^ string_of_int i


let rec subst s t =
  if Subst.is_empty s then t else
  match t with
  | Var (y, ts) when Subst.mem y s -> Subst.find y s (List.map (subst s) ts)
  | Var (y, ts) -> Var (y, List.map (subst s) ts)
  | Bot | Null | Bool | Byte | Int | Float | Text | Obj | Boxed -> t
  | Box t -> Box (subst s t)
  | Tup ts -> Tup (List.map (subst s) ts)
  | Array (t, m) -> Array (subst s t, m)
  | Func (ys, ts1, t2) ->
    let ys' = List.map fresh ys in
    let s' = adjoin_subst s (typ_subst ys (List.map var ys')) in
    Func (ys', List.map (subst s') ts1, subst s' t2)
  | Inst (c, ts) -> Inst ((*subst_cls s*) c, List.map (subst s) ts)
  | Class c -> Class (subst_cls s c)

and subst_cls s c =
  if Env.Set.subset (Env.Map.dom s) (Env.Set.of_list c.tparams) then c else
  let ys' = List.map fresh c.tparams in
  let s' = adjoin_subst s (typ_subst c.tparams (List.map var ys')) in
  { c with
    tparams = ys';
    vparams = List.map (subst s') c.vparams;
    sup = subst s' c.sup;
    def = List.map (fun (x, (sort, t)) -> (x, (sort, subst s' t))) c.def;
  }


(* Equivalence and Subtyping *)

let sup_cls c ts =
  subst (typ_subst c.tparams ts) c.sup

let eq_cls c1 c2 = c1.name = c2.name && c1.id = c2.id

let rec eq t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Var (y1, ts1), Var (y2, ts2) -> y1 = y2 && List.for_all2 eq ts1 ts2
  | Box t1', Box t2' -> eq t1' t2'
  | Tup ts1, Tup ts2 ->
    List.length ts1 = List.length ts2 && List.for_all2 eq ts1 ts2
  | Array (t1', m1), Array (t2', m2) -> eq t1' t2' && m1 = m2
  | Func (ys1, ts11, t12), Func (ys2, ts21, t22) ->
    List.length ys1 = List.length ys2 &&
    List.length ts11 = List.length ts21 &&
    let ys' = List.map var (List.map fresh ys1) in
    let s1 = typ_subst ys1 ys' in
    let s2 = typ_subst ys2 ys' in
    List.for_all2 eq (List.map (subst s1) ts11) (List.map (subst s2) ts21) &&
    eq (subst s1 t12) (subst s2 t22)
  | Inst (c1, ts1), Inst (c2, ts2) -> eq_cls c1 c2 && List.for_all2 eq ts1 ts2
  | Class c1, Class c2 -> eq_cls c1 c2
  | t1, t2 -> t1 = t2

let rec sub t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Bot, _ -> true
  | (Bool | Byte | Int | Float), Boxed -> false
  | _, Boxed -> true
  | Null, t2 -> sub t2 Boxed
  | Inst _, Obj -> true
  | Box t1', Box t2' -> sub t1' t2'
  | Tup ts1, Tup ts2 ->
    List.length ts1 = List.length ts2 && List.for_all2 sub ts1 ts2
  | Array (t1', _), Array (t2', Const) -> sub t1' t2'
  | Inst (c1, ts1), Inst (c2, ts2) ->
    eq_cls c1 c2 && List.for_all2 eq ts1 ts2 || sub (sup_cls c1 ts1) t2
  | t1, t2 -> eq t1 t2

let rec lub t1 t2 =
  if sub t1 t2 then t2 else
  if sub t2 t1 then t1 else
  match t1, t2 with
  | Box t1', Box t2' -> Box (lub t1' t2')
  | Array (t1', Const), Array (t2', Const) -> Array (lub t1' t2', Const)
  | Inst (c1, ts1), Inst (c2, ts2) -> lub (sup_cls c1 ts1) (sup_cls c2 ts2)
  | Tup ts1, Tup ts2 when List.length ts1 = List.length ts2 ->
    Tup (List.map2 lub ts1 ts2)
  | _, _ -> failwith "lub"


(* Classes *)

let gen_cls id y ys =
  { name = y;
    id = Hashtbl.hash id;
    tparams = ys;
    vparams = [];
    sup = Obj;
    def = [];
  }

let sup_cls c =
  match c.sup with
  | Obj -> None
  | Inst (c', _) -> Some c'
  | _ -> assert false

let rec cls_depth c =
  match c.sup with
  | Obj -> 1
  | Inst (c', _) -> 1 + cls_depth c'
  | _ -> assert false
