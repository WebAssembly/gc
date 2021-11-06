module T = Type

exception Error of Source.region * string


(* Variables and Paths *)

type var = (string, unit) Source.phrase

type 'a path = (path', 'a) Source.phrase
and path' =
  | PlainP of var
  | QualP of mod_path * var

and val_path = T.poly path
and typ_path = T.con path
and mod_path = T.sig_ path
and sig_path = T.sig_ path


(* Types *)

type typ = (typ', T.typ) Source.phrase
and typ' =
  | VarT of var
  | ConT of typ_path * typ list
  | BoolT
  | ByteT
  | IntT
  | FloatT
  | TextT
  | RefT of typ
  | TupT of typ list
  | FunT of typ * typ
  | PackT of sig_


(* Patterns *)

and lit =
  | BoolL of bool
  | IntL of int32
  | FloatL of float
  | TextL of string

and pat = (pat', T.typ) Source.phrase
and pat' =
  | WildP
  | VarP of var
  | LitP of lit
  | ConP of val_path * pat list
  | RefP of pat
  | TupP of pat list
  | AnnotP of pat * typ


(* Expressions *)

and unop = PosOp | NegOp | InvOp | NotOp
and binop =
  | AddOp | SubOp | MulOp | DivOp | ModOp
  | AndOp | OrOp | XorOp | ShlOp | ShrOp | CatOp
and relop = EqOp | NeOp | LtOp | GtOp | LeOp | GeOp
and logop = AndThenOp | OrElseOp

and exp = (exp', T.typ) Source.phrase
and exp' =
  | VarE of val_path
  | LitE of lit
  | ConE of val_path
  | UnE of unop * exp
  | BinE of exp * binop * exp
  | RelE of exp * relop * exp
  | LogE of exp * logop * exp
  | RefE of exp
  | DerefE of exp
  | AssignE of exp * exp
  | TupE of exp list
  | FunE of pat * exp
  | AppE of exp * exp
  | AnnotE of exp * typ
  | IfE of exp * exp * exp
  | CaseE of exp * (pat * exp) list
  | PackE of mod_ * sig_
  | LetE of dec list * exp


(* Declarations *)

and dec = (dec', T.typ * T.str) Source.phrase
and dec' =
  | ExpD of exp
  | AssertD of exp
  | ValD of pat * exp
  | TypD of var * var list * typ
  | DatD of var * var list * con list
  | ModD of var * mod_
  | SigD of var * sig_
  | RecD of dec list
  | InclD of mod_

and con = (var * typ list, T.typ) Source.phrase


(* Signatures *)

and spec = (spec', T.str) Source.phrase
and spec' =
  | ValS of var * var list * typ
  | TypS of var * var list * typ option
  | DatS of var * var list * con list
  | ModS of var * sig_
  | SigS of var * sig_
  | RecS of spec list
  | InclS of sig_

and sig_ = (sig', T.sig_) Source.phrase
and sig' =
  | ConS of sig_path
  | StrS of spec list
  | FunS of var * sig_ * sig_
  | WithS of sig_ * typ_path * var list * typ


(* Modules *)

and mod_ = (mod', T.sig_) Source.phrase
and mod' =
  | VarM of mod_path
  | StrM of dec list
  | FunM of var * sig_ * mod_
  | AppM of mod_ * mod_
  | AnnotM of mod_ * sig_
  | UnpackM of exp * sig_
  | LetM of dec list * mod_


(* Programs *)

type imp = (imp', T.str) Source.phrase
and imp' =
  | ImpD of var * string

type prog = (prog', T.typ * T.str) Source.phrase
and prog' =
  | Prog of imp list * dec list


(* Free variables *)

module Vars = Env.Map

type vars = {vals : T.typ Vars.t; mods : T.sig_ Vars.t}

let cardinal s = Vars.cardinal s.vals + Vars.cardinal s.mods
let empty = {vals = Vars.empty; mods = Vars.empty}
let (++) s1 s2 =
  Vars.{ vals = adjoin s1.vals s2.vals; mods = adjoin s1.mods s2.mods }
let (--) s1 s2 =
  Vars.{ vals = diff s1.vals s2.vals; mods = diff s1.mods s2.mods }

let list f xs = List.fold_left (++) empty (List.map f xs)

let val_var x t = {empty with vals = Vars.singleton x.Source.it t}
let mod_var x s = {empty with mods = Vars.singleton x.Source.it s}


let rec bound_pat p =
  match p.Source.it with
  | WildP | LitP _ -> empty
  | VarP x -> val_var x (Source.et p)
  | ConP (_, ps) | TupP ps -> list bound_pat ps
  | RefP p1 | AnnotP (p1, _) -> bound_pat p1

let bound_con t c =
  let (x, ts) = c.Source.it in
  val_var x (Source.et c)

let rec bound_dec d =
  let open Source in
  match d.it with
  | ExpD _ | AssertD _ | TypD _ | SigD _ -> empty
  | ValD (p, _) -> bound_pat p
  | DatD (y, ys, cs) ->
    let t = T.Var (y.it, List.map T.var (List.map Source.it ys)) in
    list (bound_con t) cs
  | ModD (x, m) -> mod_var x (Source.et m)
  | RecD ds -> list bound_dec ds
  | InclD m ->
    let _, str = T.as_str (Source.et m) in
    { vals = Env.Map.map (fun pt -> snd (T.as_poly pt.it)) str.Env.vals;
      mods = Env.Map.map Source.it str.Env.mods;
    }


let rec free_mod_path q =
  match q.Source.it with
  | PlainP x -> mod_var x (Source.et q)
  | QualP (q', _) -> free_mod_path q'

let free_val_path q =
  match q.Source.it with
  | PlainP x -> val_var x (snd (T.as_poly (Source.et q)))
  | QualP (q', _) -> free_mod_path q'

let rec free_pat p =
  match p.Source.it with
  | WildP | LitP _ | VarP _ -> empty
  | ConP (q, ps) -> free_val_path q ++ list free_pat ps
  | TupP ps -> list free_pat ps
  | RefP p1 | AnnotP (p1, _) -> free_pat p1

let rec free_exp e =
  match e.Source.it with
  | LitE _ -> empty
  | VarE q | ConE q -> free_val_path q
  | UnE (_, e1) | RefE e1 | DerefE e1 | AnnotE (e1, _) -> free_exp e1
  | BinE (e1, _, e2) | RelE (e1, _, e2) | LogE (e1, _, e2)
  | AssignE (e1, e2) | AppE (e1, e2) -> free_exp e1 ++ free_exp e2
  | TupE es -> list free_exp es
  | FunE (p1, e2) -> free_case (p1, e2)
  | IfE (e1, e2, e3) -> free_exp e1 ++ free_exp e2 ++ free_exp e3
  | CaseE (e1, pes) -> free_exp e1 ++ list free_case pes
  | PackE (m, _) -> free_mod m
  | LetE (ds, e1) -> free_exp e1 -- list bound_dec ds ++ free_decs ds

and free_case (p, e) =
  free_exp e -- bound_pat p ++ free_pat p

and free_dec d =
  match d.Source.it with
  | ExpD e | AssertD e -> free_exp e
  | ValD (p, e) -> free_exp e
  | TypD _ | DatD _ | SigD _ -> empty
  | ModD (x, m) -> free_mod m
  | RecD ds -> list free_dec ds -- list bound_dec ds
  | InclD m -> free_mod m

and free_decs = function
  | [] -> empty
  | d::ds -> free_decs ds -- bound_dec d ++ free_dec d

and free_mod m =
  match m.Source.it with
  | VarM q -> free_mod_path q
  | StrM ds -> free_decs ds
  | FunM (x, s, m) -> free_mod m -- mod_var x (Source.et s)
  | AppM (m1, m2) -> free_mod m1 ++ free_mod m2
  | AnnotM (m1, _) -> free_mod m1
  | UnpackM (e, _) -> free_exp e
  | LetM (ds, m1) -> free_mod m1 -- list bound_dec ds ++ free_decs ds
