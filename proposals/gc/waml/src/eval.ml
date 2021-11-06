open Source
open Syntax

module V = Value
module S = Env


(* Error handling *)

exception Trap of Source.region * string
exception Crash of Source.region * string

let trap at fmt = Printf.ksprintf (fun s -> raise (Trap (at, s))) fmt
let crash at fmt = Printf.ksprintf (fun s -> raise (Crash (at, s))) fmt


(* Environments *)

type env = (Value.value, unit, Value.module_, unit) Env.env

module E =
struct
  include Env

  let to_vals env = List.map (fun (x, v) -> (x, v.it)) (vals env)
  let of_vals xvs at =
    let xs, vs = List.split xvs in
    extend_vals empty (List.map (fun x -> x @@ at) xs) vs
end


(* Paths *)

let eval_val_var env x : V.value =
  match E.find_opt_val x env with
  | Some v -> v.it
  | None -> crash x.at "unknown value identifier `%s`" x.it

let eval_mod_var env x : V.module_ =
  match E.find_opt_mod x env with
  | Some m -> m.it
  | None -> crash x.at "unknown module identifier `%s`" x.it

let rec eval_val_path env q : V.value =
  match q.it with
  | PlainP x -> eval_val_var env x
  | QualP (q1, x) ->
    match eval_mod_path env q1 with
    | V.Str s ->
      (match S.find_opt_val x s with
      | Some v -> v.it
      | None -> crash x.at "unknown value component `%s`" x.it
      )
    | _ -> crash q1.at "runtime error in path"

and eval_mod_path env q : V.module_ =
  match q.it with
  | PlainP x -> eval_mod_var env x
  | QualP (q1, x) ->
    match eval_mod_path env q1 with
    | V.Str s ->
      (match S.find_opt_mod x s with
      | Some m -> m.it
      | None -> crash x.at "unknown module component `%s`" x.it
      )
    | _ -> crash q1.at "runtime error in path"

let eval_con_path env q : string =
  match q.it with
  | PlainP x -> x.it
  | QualP (_, x) -> x.it


(* Patterns *)

let eval_lit _env lit : V.value =
  match lit with
  | BoolL b -> V.of_bool b
  | IntL i -> V.int i
  | FloatL z -> V.Float z
  | TextL t -> V.Text t


let rec eval_pat env p v : env option =
  match p.it, v with
  | WildP, _ ->
    Some E.empty

  | VarP x, _ ->
    Some (E.singleton_val x v)

  | LitP l, v ->
    let v' = eval_lit env l in
    if V.eq v v' then Some E.empty else None

  | ConP (q, ps), V.Con (x, vs) ->
    let x' = eval_con_path env q in
    if x <> x' then None else
    eval_pats env ps vs p.at

  | RefP p, V.Ref r ->
    eval_pat env p !r

  | TupP ps, V.Tup vs ->
    eval_pats env ps vs p.at

  | AnnotP (p1, _), v ->
    eval_pat env p1 v

  | _, _ ->
    None

and eval_pats env ps vs at : env option =
  match ps, vs with
  | [], [] -> Some E.empty
  | p1::ps', v1::vs' ->
    (match eval_pat env p1 v1, eval_pats env ps' vs' at with
    | Some env1, Some env2 -> Some (E.disjoint_union env1 env2)
    | _, _ -> None
    )
  | _, _ -> trap at "runtime error at tuple pattern"


(* Expressions *)

let rec eval_exp env e : V.value =
  match e.it with
  | VarE q ->
    eval_val_path env q

  | LitE l ->
    eval_lit env l

  | ConE q ->
    let x' = eval_con_path env q in
    V.Con (x', [])

  | UnE (op, e1) ->
    let v1 = eval_exp env e1 in
    (match op, v1 with
    | PosOp, V.Int i -> V.int i
    | PosOp, V.Float z -> V.Float z
    | NegOp, V.Int i -> V.int (Int32.neg i)
    | NegOp, V.Float z -> V.Float (-.z)
    | InvOp, V.Int i -> V.int (Int32.lognot i)
    | NotOp, v1 when V.is_bool v1 -> V.of_bool (not (V.to_bool v1))
    | _ -> crash e.at "runtime type error at unary operator"
    )

  | BinE (e1, op, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match op, v1, v2 with
    | AddOp, V.Int i1, V.Int i2 -> V.int (Int32.add i1 i2)
    | SubOp, V.Int i1, V.Int i2 -> V.int (Int32.sub i1 i2)
    | MulOp, V.Int i1, V.Int i2 -> V.int (Int32.mul i1 i2)
    | DivOp, V.Int i1, V.Int i2 ->
      if i2 = 0l then trap e.at "division by zero" else
      V.int (Int32.div i1 i2)
    | ModOp, V.Int i1, V.Int i2 ->
      if i2 = 0l then trap e.at "modulo by zero" else
      V.int (Int32.rem i1 i2)
    | AndOp, V.Int i1, V.Int i2 -> V.int (Int32.logand i1 i2)
    | OrOp,  V.Int i1, V.Int i2 -> V.int (Int32.logor i1 i2)
    | XorOp, V.Int i1, V.Int i2 -> V.int (Int32.logxor i1 i2)
    | ShlOp, V.Int i1, V.Int i2 ->
      V.int Int32.(shift_left i1 (to_int i2 land 0x1f))
    | ShrOp, V.Int i1, V.Int i2 ->
      V.int Int32.(shift_right i1 (to_int i2 land 0x1f))
    | AddOp, V.Float z1, V.Float z2 -> V.Float (z1 +. z2)
    | SubOp, V.Float z1, V.Float z2 -> V.Float (z1 -. z2)
    | MulOp, V.Float z1, V.Float z2 -> V.Float (z1 *. z2)
    | DivOp, V.Float z1, V.Float z2 -> V.Float (z1 /. z2)
    | CatOp, V.Text t1, V.Text t2 -> V.Text (t1 ^ t2)
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | RelE (e1, op, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match op with
    | EqOp -> V.of_bool (V.eq v1 v2)
    | NeOp -> V.of_bool (not (V.eq v1 v2))
    | LtOp -> V.of_bool (v1 < v2)
    | GtOp -> V.of_bool (v1 > v2)
    | LeOp -> V.of_bool (v1 <= v2)
    | GeOp -> V.of_bool (v1 >= v2)
    )

  | LogE (e1, AndThenOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | v1 when V.is_bool v1 && not (V.to_bool v1) -> v1
    | v1 when V.is_bool v1 && V.to_bool v1 -> eval_exp env e2
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | LogE (e1, OrElseOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | v1 when V.is_bool v1 && V.to_bool v1 -> v1
    | v1 when V.is_bool v1 && not (V.to_bool v1) -> eval_exp env e2
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | RefE e1 ->
    let v1 = eval_exp env e1 in
    V.Ref (ref v1)

  | DerefE e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Ref r -> !r
    | _ -> crash e.at "runtime type error at dereferencing"
    )

  | AssignE (e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1 with
    | V.Ref r1 -> r1 := v2; V.Tup []
    | _ -> crash e.at "runtime type error at dereferencing"
    )

  | TupE es ->
    let vs = List.map (eval_exp env) es in
    V.Tup vs

  | FunE (p1, e2) ->
    let f xvs v1 =
      let xvs' = List.map (fun (x, v) -> x, V.fix xvs v) xvs in
      let env' = E.adjoin env (E.of_vals xvs' e.at) in
      match eval_pat (E.adjoin env env') p1 v1 with
      | Some env1 -> eval_exp (E.adjoin (E.adjoin env env') env1) e2
      | None -> trap e.at "pattern match failure for function argument"
    in V.Fun f

  | AppE (e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1 with
    | V.Fun f1 -> f1 [] v2
    | V.Con (x', vs) -> V.Con (x', vs @ [v2])
    | _ -> crash e.at "runtime type error at function application"
    )

  | AnnotE (e1, _t) ->
    eval_exp env e1

  | IfE (e1, e2, e3) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | v1 when V.is_bool v1 && V.to_bool v1 -> eval_exp env e2
    | v1 when V.is_bool v1 && not (V.to_bool v1) -> eval_exp env e3
    | _ -> crash e.at "runtime type error at conditional"
    )

  | CaseE (e1, pes) ->
    let v1 = eval_exp env e1 in
    let rec cases = function
      | [] -> trap e.at "pattern match failure for case scrutinee"
      | (pI, eI)::pes' ->
        match eval_pat env pI v1 with
        | Some env' -> eval_exp (E.adjoin env env') eI
        | None -> cases pes'
    in cases pes

  | PackE (m, _) ->
    let m' = eval_mod env m in
    V.Pack m'

  | LetE (ds, e1) ->
    let _, env' = eval_decs env ds (V.Tup []) in
    eval_exp (E.adjoin env env') e1


(* Modules *)

and eval_mod env m : V.module_ =
  match m.it with
  | VarM q ->
    eval_mod_path env q

  | StrM ds ->
    let _, env' = eval_decs env ds (V.Tup []) in
    V.Str env'

  | FunM (x1, _, m2) ->
    let f m1 = eval_mod (E.extend_mod env x1 m1) m2 in
    V.Fct f

  | AppM (m1, m2) ->
    let m1' = eval_mod env m1 in
    let m2' = eval_mod env m2 in
    (match m1' with
    | V.Fct f1 -> f1 m2'
    | _ -> crash m.at "runtime type error at functor application"
    )

  | AnnotM (m1, _) ->
    eval_mod env m1

  | UnpackM (e, _) ->
    let v = eval_exp env e in
    (match v with
    | V.Pack m -> m
    | _ -> crash m.at "runtime type error at unpack"
    )

  | LetM (ds, m1) ->
    let _, env' = eval_decs env ds (V.Tup []) in
    eval_mod (E.adjoin env env') m1


(* Declarations *)

and eval_dec env d : V.value * env =
  match d.it with
  | ExpD e1 ->
    let v1 = eval_exp env e1 in
    v1, E.empty

  | AssertD e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | v1 when V.is_bool v1 && V.to_bool v1 -> V.Tup [], E.empty
    | v1 when V.is_bool v1 && not (V.to_bool v1) -> trap d.at "assertion failure"
    | _ -> crash d.at "runtime type error at assertion"
    )

  | ValD (p, e) ->
    let v = eval_exp env e in
    (match eval_pat env p v with
    | Some env' -> V.Tup [], env'
    | None -> trap e.at "pattern match failure for value binding"
    )

  | TypD _ ->
    V.Tup [], E.empty

  | DatD (_, _, cs) ->
    let env' =
      List.fold_left (fun env' c ->
        let (x, ts) = c.it in
        E.extend_val env' x (V.con x.it (List.length ts))
      ) E.empty cs
    in V.Tup [], env'

  | ModD (x, m) ->
    let m = eval_mod env m in
    V.Tup [], E.singleton_mod x m

  | SigD _ ->
    V.Tup [], E.empty

  | RecD ds ->
    let _, env' = eval_decs env ds (V.Tup []) in
    V.Tup [], E.map_vals (V.fix (E.to_vals env')) env'

  | InclD m ->
    match eval_mod env m with
    | V.Str env' ->
      V.Tup [], env'
    | _ -> crash d.at "runtime error at include"

and eval_decs env ds v : V.value * env =
  match ds with
  | [] -> v, E.empty
  | d::ds' ->
    let v1, env1 = eval_dec env d in
    let v2, env2 = eval_decs (E.adjoin env env1) ds' v1 in
    v2, E.adjoin env1 env2


(* Programs *)

let get_env = ref (fun _at _url -> failwith "get_env")

let eval_imp env env' d : env =
  let ImpD (x, url) = d.it in
  let s = !get_env d.at url in
  E.extend_mod env' x (V.Str s)

let env0 =
  let at = Prelude.region in
  List.fold_right (fun (x, l) env ->
    E.extend_val env (x @@ at) (eval_lit env l)
  ) Prelude.vals E.empty

let eval_prog env p : V.value * env =
  let Prog (is, ds) = p.it in
  let env' = Env.adjoin env0 env in
  let env1 = List.fold_left (eval_imp env') E.empty is in
  let v, env2 = eval_decs (E.adjoin env' env1) ds (V.Tup []) in
  v, E.adjoin env1 env2
