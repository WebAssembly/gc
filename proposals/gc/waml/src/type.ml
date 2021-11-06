open Source

module S = Env


(* Types *)

type var = string
type pred = Any | Eq | Ord | Num
type arity = UnknownArity | KnownArity of int | VariableArity

type typ =
  | Var of var * typ list
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Ref of typ
  | Tup of typ list
  | Fun of typ * typ * arity ref
  | Data of typ
  | Pack of sig_
  | Infer of infer ref

and infer =
  | Unres of string * pred
  | Res of typ

and poly = Forall of var list * typ
and con = Lambda of var list * typ

and sig_ =
  | Str of var list * str
  | Fct of var list * sig_ * sig_

and str = (poly, con, sig_, sig_) Env.env


(* Constructors and Accessors *)

let var b = Var (b, [])

let rec fun_flat ts t =
  match ts with
  | [] -> t
  | t'::ts' -> Fun (t', fun_flat ts' t, ref VariableArity)

let is_fun = function Fun _ -> true | _ -> false

let as_tup = function Tup ts -> ts | _ -> assert false
let as_fun = function Fun (t1, t2, a) -> t1, t2, a | _ -> assert false
let as_data = function Data t -> t | _ -> assert false

let rec as_fun_flat t = as_fun_flat' [] t
and as_fun_flat' ts = function
  | Fun (t1, t2, _) -> as_fun_flat' (t1::ts) t2
  | Infer {contents = Res t'} -> as_fun_flat' ts t'
  | t -> List.rev ts, t

let as_poly (Forall (bs, t)) = bs, t
let as_mono (Forall (_, t)) = t

let as_str = function Str (bs, s) -> bs, s | _ -> assert false
let as_fct = function Fct (bs, s1, s2) -> bs, s1, s2 | _ -> assert false


(* Printing *)

let list sep f xs = String.concat sep (List.map f xs)

let string_of_pred = function
  | Any -> "any"
  | Eq -> "eq"
  | Ord -> "ord"
  | Num -> "num"

let string_of_arity a =
  match !a with
  | UnknownArity -> "?"
  | KnownArity i -> string_of_int i
  | VariableArity -> ""

let quant sym = function
  | [] -> ""
  | bs -> sym ^ list " " Fun.id bs ^ ". "

let rec string_of_typ = function
  | Fun (t1, t2, a) ->
    string_of_typ_app t1 ^ " ->" ^ string_of_arity a ^ " " ^ string_of_typ t2
  | Data t -> "data " ^ string_of_typ t
  | Pack s -> "pack " ^ string_of_sig s
  | Infer {contents = Res t'} -> string_of_typ t'
  | t -> string_of_typ_app t

and string_of_typ_app = function
  | Var (b, ts) -> list " " string_of_typ_simple (var b :: ts)
  | Ref t -> "ref " ^ string_of_typ_simple t
  | Infer {contents = Res t'} -> string_of_typ_app t'
  | t -> string_of_typ_simple t

and string_of_typ_simple = function
  | Var (b, []) -> b
  | Bool -> "Bool"
  | Byte -> "Byte"
  | Int -> "Int"
  | Float -> "Float"
  | Text -> "Text"
  | Tup ts -> "(" ^ list ", " string_of_typ ts ^ ")"
  | Infer {contents = Res t'} -> string_of_typ_simple t'
  | Infer {contents = Unres (y, Any)} -> "_" ^ y
  | Infer {contents = Unres (y, p)} -> "(_" ^ y ^ " " ^ string_of_pred p ^ ")"
  | t -> "(" ^ string_of_typ t ^ ")"

and string_of_poly (Forall (bs, t)) = quant "" bs ^ string_of_typ t
and string_of_con (Lambda (bs, t)) = quant "\\" bs ^ string_of_typ t

and string_of_sig = function
  | Str (bs, str) ->
    quant "?" bs ^ "{" ^ string_of_str' "; " str ^ "}"
  | Fct (bs, s1, s2) ->
    quant "!" bs ^ "(" ^ string_of_sig s1 ^ " -> " ^ string_of_sig s2 ^ ")"

and string_of_str' sep str =
  let vs = List.map string_of_sval (S.vals str) in
  let ts = List.map string_of_styp (S.typs str) in
  let ms = List.map string_of_smod (S.mods str) in
  let ss = List.map string_of_ssig (S.sigs str) in
  let xs = List.sort compare_by_region (ss @ ms @ ts @ vs) in
  String.concat sep (List.map it xs)

and string_of_sval (x, pt) =
  ("val " ^ x ^ " : " ^ string_of_poly pt.it) @@ pt.at
and string_of_styp (y, {it = Lambda (bs, t); at; _}) =
  ("type " ^ list " " Fun.id (y :: bs) ^ " = " ^ string_of_typ t) @@ at
and string_of_smod (x, s) =
  ("module " ^ x ^ " : " ^ string_of_sig s.it) @@ s.at
and string_of_ssig (y, s) =
  ("signature " ^ y ^ " = " ^ string_of_sig s.it) @@ s.at

let string_of_str = string_of_str' "\n"


(* Free variables *)

module Set = Env.Set
let (++) = Set.union

let list f ts = List.fold_left (++) Set.empty (List.map f ts)

let rec free = function
  | Var (b, ts) -> Set.singleton b ++ list free ts
  | Bool | Byte | Int | Float | Text -> Set.empty
  | Ref t | Data t-> free t
  | Tup ts -> list free ts
  | Fun (t1, t2, _) -> free t1 ++ free t2
  | Pack s -> free_sig s
  | Infer {contents = Res t'} -> free t'
  | Infer _ -> Set.empty

and free_poly (Forall (bs, t)) = Set.diff (free t) (Set.of_list bs)
and free_con (Lambda (bs, t)) = Set.diff (free t) (Set.of_list bs)

and free_sig = function
  | Str (bs, str) -> Set.diff (free_str str) (Set.of_list bs)
  | Fct (bs, s1, s2) ->
    Set.diff (Set.union (free_sig s1) (free_sig s2)) (Set.of_list bs)

and free_str str = Set.empty
  |> S.fold_vals (fun _ t set -> set ++ free_poly t.it) str
  |> S.fold_typs (fun _ c set -> set ++ free_con c.it) str
  |> S.fold_mods (fun _ s set -> set ++ free_sig s.it) str
  |> S.fold_sigs (fun _ s set -> set ++ free_sig s.it) str


(* Free inference variables *)

let list f ts = List.concat_map f ts

let rec free_infer = function
  | Var (_, ts) -> list free_infer ts
  | Bool | Byte | Int | Float | Text -> []
  | Ref t | Data t -> free_infer t
  | Tup ts -> list free_infer ts
  | Fun (t1, t2, _) -> free_infer t1 @ free_infer t2
  | Pack s -> free_infer_sig s
  | Infer {contents = Res t'} -> free_infer t'
  | Infer inf -> [inf]

and free_infer_poly (Forall (_, t)) = free_infer t
and free_infer_con (Lambda (_, t)) = free_infer t

and free_infer_sig = function
  | Str (_, str) -> free_infer_str str
  | Fct (_, s1, s2) -> free_infer_sig s1 @ free_infer_sig s2

and free_infer_str str = []
  |> S.fold_vals (fun _ t set -> free_infer_poly t.it @ set) str
  |> S.fold_typs (fun _ c set -> free_infer_con c.it @ set) str
  |> S.fold_mods (fun _ s set -> free_infer_sig s.it @ set) str
  |> S.fold_sigs (fun _ s set -> free_infer_sig s.it @ set) str


(* Substitutions *)

module Subst = Env.Map
type subst = con Subst.t * Set.t

let is_empty_subst (m, s) = Subst.is_empty m

let empty_subst = (Subst.empty, Set.empty)
let adjoin_subst (m1, s1) (m2, s2) =
  (Subst.union (fun _ c1 c2 -> Some c2) m1 m2, Set.union s1 s2)

let lookup_subst (m, s) b = Subst.find_opt b m
let extend_subst (m, s) b c = (Subst.add b c m, Set.union s (free_con c))
let extend_subst_typ su b t =
  if t = Var (b, []) then su else extend_subst su b (Lambda ([], t))
let extend_subst_var su b b' =
  if b = b' then su else extend_subst_typ su b (var b')

let con_subst bs cs = List.fold_left2 extend_subst empty_subst bs cs
let typ_subst bs ts = List.fold_left2 extend_subst_typ empty_subst bs ts
let var_subst bs ts = List.fold_left2 extend_subst_var empty_subst bs ts


let rec fresh_for s b =
  if not (Set.mem b s) then b else
  match String.index_opt b '/' with
  | None -> fresh_for s (b ^ "/1")
  | Some i ->
    let b' = String.sub b 0 i in
    let n = int_of_string (String.sub b (i + 1) (String.length b - i - 1)) in
    fresh_for s (b' ^ "/" ^ string_of_int (n + 1))

let subst_fresh ((m, s) as su) bs =
  let bs' = List.map (fresh_for s) bs in
  let su' = adjoin_subst su (typ_subst bs (List.map var bs')) in
  su', bs'


let rec subst ((m, s) as su) t =
  if is_empty_subst su then t else
  match t with
  | Var (b, ts) when Subst.mem b m ->
    let ts' = List.map (subst su) ts in
    (match Subst.find_opt b m with
    | None -> Var (b, ts')
    | Some (Lambda ([], Var (b', []))) -> Var (b', ts')  (* Hack for higher arity *)
    | Some (Lambda (bs, t')) -> subst (typ_subst bs ts') t'
    )
  | Var (b, ts) -> Var (b, List.map (subst su) ts)
  | Bool | Byte | Int | Float | Text -> t
  | Ref t1 -> Ref (subst su t1)
  | Tup ts -> Tup (List.map (subst su) ts)
  | Fun (t1, t2, a) -> Fun (subst su t1, subst su t2, ref !a)
  | Data t1 -> Data (subst su t1)
  | Pack s -> Pack (subst_sig su s)
  | Infer {contents = Res t'} -> subst su t'
  | Infer _ -> t

and subst_poly su (Forall (bs, t)) =
  let su', bs' = subst_fresh su bs in Forall (bs', subst su' t)

and subst_con su (Lambda (bs, t)) =
  let su', bs' = subst_fresh su bs in Lambda (bs', subst su' t)

and subst_sig su s =
  if is_empty_subst su then s else
  match s with
  | Str (bs, str) ->
    let s', bs' = subst_fresh su bs in
    Str (bs', subst_str s' str)
  | Fct (bs, s1, s2) ->
    let s', bs' = subst_fresh su bs in
    Fct (bs', subst_sig s' s1, subst_sig s' s2)

and subst_str su str =
  str
  |> S.map_vals (subst_poly su)
  |> S.map_typs (subst_con su)
  |> S.map_mods (subst_sig su)
  |> S.map_sigs (subst_sig su)


(* Equivalence *)

let eq_sig = ref (fun _ -> assert false)

let rec eq t1 t2 =
  t1 == t2 ||
  match t1, t2 with
  | Var (b1, ts1), Var (b2, ts2) -> b1 = b2 && List.for_all2 eq ts1 ts2
  | Ref t1', Ref t2' -> eq t1' t2'
  | Tup ts1, Tup ts2 ->
    List.length ts1 = List.length ts2 && List.for_all2 eq ts1 ts2
  | Fun (t11, t12, a1), Fun (t21, t22, a2) ->
    assert (!a1 = !a2);
    eq t11 t21 && eq t12 t22
  | Data t1', Data t2' -> eq t1' t2'
  | Pack s1, Pack s2 -> !eq_sig s1 s2
  | Infer {contents = Res t1'}, t2 -> eq t1' t2
  | t1, Infer {contents = Res t2'} -> eq t1 t2'
  | t1, t2 -> t1 = t2

let eq_con (Lambda (bs1, t1)) (Lambda (bs2, t2)) =
  List.length bs1 = List.length bs2 &&
  let ts = List.map var bs1 in
  eq (subst (typ_subst bs1 ts) t1) (subst (typ_subst bs2 ts) t2)


(* Instantiation and Generalization *)

let infer_ctr = ref 0

let infer' p b = Infer (ref (Unres (b, p)))
let infer p = incr infer_ctr; infer' p ("a" ^ string_of_int !infer_ctr)

let inst (Forall (bs, t)) =
  match subst (typ_subst bs (List.map (infer' Any) bs)) t with
  | Fun (t1, t2, a) -> Fun (t1, t2, ref !a)
  | t' -> t'

let list f capt free i ts =
  List.fold_left Set.union Set.empty (List.map (f capt free i) ts)

let rec generalize' capt free i = function
  | Var (b, ts) -> list generalize' capt free i ts
  | Bool | Byte | Int | Float | Text -> Set.empty
  | Ref t | Data t -> generalize' capt free i t
  | Tup ts -> list generalize' capt free i ts
  | Fun (t1, t2, arity) ->
    if !arity = UnknownArity then arity := VariableArity;
    let set1 = generalize' capt free i t1 in
    let set2 = generalize' capt free i t2 in
    set1 ++ set2
  | Pack s -> generalize_sig capt free i s
  | Infer {contents = Res t'} -> generalize' capt free i t'
  | Infer ({contents = Unres (b, p)} as inf) ->
    if p <> Any || List.memq inf (Lazy.force capt) then Set.empty else
    let c = String.make 1 (Char.chr (Char.code 'a' + !i mod 26)) in
    let b = if !i < 26 then c else c ^ string_of_int (!i / 26) in
    incr i;
    inf := Res (var (fresh_for free b));
    Set.singleton b

and generalize_poly capt free i (Forall (bs, t)) =
  generalize' capt (List.fold_right Set.add bs free) i t

and generalize_sig capt free i = function
  | Str (bs, str) -> generalize_str capt (List.fold_right Set.add bs free) i str
  | Fct (bs, s1, s2) ->
    let free' = List.fold_right Set.add bs free in
    generalize_sig capt free' i s1 ++ generalize_sig capt free' i s2

and generalize_str capt free i str = Set.empty
  |> S.fold_vals (fun _ t set -> set ++ generalize_poly capt free i t.it) str
  |> S.fold_mods (fun _ s set -> set ++ generalize_sig capt free i s.it) str

let generalize env = function
  | Forall ([], t) ->
    let bs = generalize' (lazy (free_infer_str env)) (free t) (ref 0) t in
    Forall (Set.elements bs, t)
  | t -> t


(* Defaulting inference variables *)

let rec default = function
  | Var (_, ts) -> List.iter default ts
  | Bool | Byte | Int | Float | Text -> ()
  | Ref t | Data t -> default t
  | Tup ts -> List.iter default ts
  | Fun (t1, t2, _) -> default t1; default t2
  | Pack s -> default_sig s
  | Infer {contents = Res t} -> default t
  | Infer inf -> inf := Res Int

and default_poly (Forall (_, t)) = default t

and default_sig = function
  | Str (_, str) -> default_str str
  | Fct (_, s1, s2) -> default_sig s1; default_sig s2

and default_str str =
  S.iter_vals (fun _ t -> default_poly t.it) str;
  S.iter_mods (fun _ s -> default_sig s.it) str


(* Unification *)

exception Unify of typ * typ
exception Unsatisfiable

(*
let rec enforce p = function
  | Var _ | Fun _ when p = Any -> ()
  | Int | Float -> ()
  | Bool | Byte | Text | Ref _ when p <= Eq -> ()
  | Tup ts -> List.iter (enforce p) ts
  | Infer {contents = Res t'} -> enforce p t'
  | Infer ({contents = Unres (y, p')} as inf) -> inf := Unres (y, max p p')
  | _ -> raise Unsatisfiable

let rec occurs inf = function
  | Var (_, ts) | Tup ts -> List.exists (f inf) ts
  | Bool | Byte | Int | Float | Text -> false
  | Ref t -> occurs inf t
  | Fun (t1, t2, _) -> occurs inf t1 || occurs inf t2
  | Infer {contents = Res t} -> occurs inf t
  | Infer ({contents = Unres _} as inf') -> inf == inf'
*)

let rec enforce inf (p : pred) = function
  | Var (_, ts) when p = Any -> List.iter (enforce inf p) ts
  | Int | Float -> ()
  | Bool | Byte | Text when p <= Eq -> ()
  | Ref t when p <= Eq -> enforce inf p t
  | Tup ts -> List.iter (enforce inf p) ts
  | Fun (t1, t2, _) when p = Any -> enforce inf p t1; enforce inf p t2
  | Data t when p = Any -> enforce inf p t
  | Pack s when p = Any -> ()
  | Infer {contents = Res t'} -> enforce inf p t'
  | Infer ({contents = Unres (y, p')} as inf') when inf' != inf ->
    inf' := Unres (y, max p p')
  | _ -> raise Unsatisfiable

let rec unify t1 t2 =
  if t1 != t2 then
  match t1, t2 with
  | Var (b1, ts1), Var (b2, ts2) when b1 = b2 -> List.iter2 unify ts1 ts2
  | Ref t1', Ref t2' -> unify t1' t2'
  | Tup ts1, Tup ts2 when List.length ts1 = List.length ts2 ->
    List.iter2 unify ts1 ts2
  | Fun (t11, t12, a1), Fun (t21, t22, a2) ->
    let a' =
      match !a1, !a2 with
      | UnknownArity, a | a, UnknownArity -> a
      | VariableArity, _ | _, VariableArity -> VariableArity
      | KnownArity n1, KnownArity n2 ->
        if n1 = n2 then KnownArity n1 else VariableArity
    in a1 := a'; a2 := a';
    unify t11 t21; unify t12 t22
  | Data t1', Data t2' -> unify t1' t2'
  | Pack s1, Pack s2 ->
    if not (!eq_sig s1 s2) then raise (Unify (t1, t2))
  | Infer {contents = Res t1'}, t2 -> unify t1' t2
  | t1, Infer {contents = Res t2'} -> unify t1 t2'
  | Infer ({contents = Unres _} as inf1), Infer ({contents = Unres _} as inf2)
    when inf1 == inf2 -> ()
  | Infer ({contents = Unres (b, p)} as inf1), t2 ->
    (try enforce inf1 p t2 with Unsatisfiable -> raise (Unify (t1, t2)));
    inf1 := Res t2
  | t1, Infer {contents = Unres _} -> unify t2 t1
  | _ -> raise (Unify (t1, t2))

let rec norm = function
  | Infer {contents = Res t} -> norm t
  | t -> t


let sub_poly (Forall (bs1, t1) as pt1) (Forall (bs2, t2)) =
  let bs2' = List.map (fresh_for (free t1)) bs2 in
  try unify (inst pt1) (subst (var_subst bs2 bs2') t2); true with Unify _ -> false


(* Signature Operations *)

let pack bs s =
  match bs, s with
  | [], s -> s
  | bs, Str ([], str) -> Str (bs, str)
  | _ -> assert false

let unpack x = function
  | Str (bs, str) ->
    let free = free_str str in
    let bs' = List.map (fun b -> fresh_for free (x ^ "." ^ b)) bs in
    bs', Str ([], subst_str (var_subst bs bs') str)
  | s -> [], s


(* Matching *)

exception Mismatch of string

let path p = "`" ^ String.concat "." p ^ "`"

let rec lookup p str1 str2 b : con option =
  match
    S.fold_typs (fun y c2 res ->
      if res <> None then res else
      match c2.it with
      | Lambda (bs, Var (b', ts)) when b' = b && ts = List.map var bs ->
        let p' = p @ [y] in
        (match S.find_opt_typ (y @@ c2.at) str1 with
        | Some c1 -> Some c1.it
        | None -> raise (Mismatch ("missing type member " ^ path p'))
        )
      | _ -> None
    ) str2 None
  with
  | Some c -> Some c
  | None ->
    S.fold_mods (fun x s2 res ->
      if res <> None then res else
      match s2.it with
      | Str (bs, str2') ->
        let p' = p @ [x] in
        (match S.find_opt_mod (x @@ s2.at) str1 with
        | Some {it = Str (_, str1'); _} -> lookup p' str1' str2' b
        | Some _ ->
          raise (Mismatch ("incompatible module member " ^ path p' ^
            ", due to different kind of signature"))
        | None -> raise (Mismatch ("missing module member " ^ path p'))
        )
      | _ -> None
    ) str2 None

let rec sub s1 s2 : subst =
  match s1, s2 with
  | Str (bs1, str1), Str (bs2, str2) ->
    let cs = List.map Option.get (List.map (lookup [] str1 str2) bs2) in
    let su = con_subst bs2 cs in
    sub_str [] str1 (subst_str su str2);
    su
  | Fct (bs1, s11, s12), Fct (bs2, s21, s22) ->
    let su1 = try sub (pack bs2 s21) (pack bs1 s11) with Mismatch s ->
      raise (Mismatch ("incompatible functor parameter, due to " ^ s))
    in
    let _su2 = try sub (subst_sig su1 s12) (subst_sig su1 s22) with Mismatch s ->
      raise (Mismatch ("incompatible functor result, due to " ^ s))
    in
    empty_subst
  | _, _ ->
    raise (Mismatch "different kind of signature")

and sub_str p str1 str2 =
  S.iter_vals (fun x t2 ->
    let p' = p @ [x] in
    match S.find_opt_val (x @@ t2.at) str1 with
    | None -> raise (Mismatch ("missing value member " ^ path p'))
    | Some t1 ->
      if not (sub_poly t1.it t2.it) then
        raise (Mismatch ("incompatible value member " ^ path p' ^
          ", " ^ string_of_poly t1.it ^ " vs " ^ string_of_poly t2.it))
  ) str2;
  S.iter_typs (fun y c2 ->
    let p' = p @ [y] in
    match S.find_opt_typ (y @@ c2.at) str1 with
    | None -> raise (Mismatch ("missing type member " ^ path p'))
    | Some c1 ->
      if not (eq_con c1.it c2.it) then
        raise (Mismatch ("incompatible type member " ^ path p' ^
          ", " ^ string_of_con c1.it ^ " vs " ^ string_of_con c2.it))
  ) str2;
  S.iter_mods (fun x s2 ->
    let p' = p @ [x] in
    match S.find_opt_mod (x @@ s2.at) str1 with
    | None -> raise (Mismatch ("missing module member " ^ path p'))
    | Some s1 ->
      match s1.it, s2.it with
      | Str (_, str1'), Str (_, str2') -> sub_str p' str1' str2'
      | _ ->
        try ignore (sub s1.it s2.it) with Mismatch s -> 
          raise (Mismatch ("incompatible module member " ^ path p' ^
            ", due to " ^ s))
  ) str2;
  S.iter_sigs (fun y s2 ->
    let p' = p @ [y] in
    match S.find_opt_sig (y @@ s2.at) str1 with
    | None -> raise (Mismatch ("missing signature member " ^ path p'))
    | Some s1 ->
      try ignore (sub s1.it s2.it); ignore (sub s2.it s1.it) with Mismatch s -> 
        raise (Mismatch ("incompatible signature member " ^ path p' ^
          ", due to " ^ s))
  ) str2

let () = eq_sig := fun s1 s2 ->
  try ignore (sub s1 s2); ignore (sub s2 s1); true with Mismatch _ -> false
