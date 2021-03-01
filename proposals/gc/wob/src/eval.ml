open Source
open Syntax

module T = Type
module V = Value


(* Error handling *)

exception Trap of Source.region * string
exception Crash of Source.region * string
exception Return of V.value list

let trap at fmt = Printf.ksprintf (fun s -> raise (Trap (at, s))) fmt
let crash at fmt = Printf.ksprintf (fun s -> raise (Crash (at, s))) fmt


(* Environments *)

type env = (V.value ref, T.con) Env.env

module E =
struct
  include Env
  let singleton_val x v = Env.singleton_val x (ref v)
  let extend_val env x v = Env.extend_val env x (ref v)
  let extend_vals env xs vs = Env.extend_vals env xs (List.map ref vs)
  let extend_typ_gnd env y t = extend_typ env y (fun _ -> t)
  let extend_typ_abs env y = extend_typ_gnd env y (T.var y)
  let extend_typs_gnd env ys ts = List.fold_left2 extend_typ_gnd env ys ts
  let extend_typs_abs env ys = List.fold_left extend_typ_abs env ys
end


(* Types *)

let eval_typ_var env y : T.con =
  match E.find_typ y.it env with
  | Some c -> c
  | None -> crash y.at "unknown type identifier `%s`" y.it

let rec eval_typ env t : T.typ =
  match t.it with
  | VarT (y, ts) ->
    let c = eval_typ_var env y in
    c (List.map (eval_typ env) ts)
  | BoolT -> T.Bool
  | ByteT -> T.Byte
  | IntT -> T.Int
  | FloatT -> T.Float
  | TextT -> T.Text
  | ObjT -> T.Obj
  | TupT ts -> T.Tup (List.map (eval_typ env) ts)
  | ArrayT t -> T.Array (eval_typ env t)
  | FuncT (ys, ts1, ts2) ->
    let ys' = List.map Source.it ys in
    let env' = E.extend_typs_abs env ys' in
    T.Func (ys', List.map (eval_typ env') ts1, List.map (eval_typ env') ts2)


(* Expressions *)

let eval_var_ref env x : V.value ref =
  match E.find_val x.it env with
  | Some v -> v
  | None -> crash x.at "unknown value identifier `%s`" x.it

let eval_var env x : V.value =
  !(eval_var_ref env x)

let eval_lit _env lit : V.value =
  match lit with
  | NullLit -> V.Null
  | BoolLit b -> V.Bool b
  | IntLit i -> V.Int i
  | FloatLit z -> V.Float z
  | TextLit t -> V.Text t


let rec eval_exp env e : V.value =
  match e.it with
  | VarE x ->
    eval_var env x

  | LitE l ->
    eval_lit env l

  | UnE (op, e1) ->
    let v1 = eval_exp env e1 in
    (match op, v1 with
    | PosOp, V.Int i -> V.Int i
    | PosOp, V.Float z -> V.Float z
    | NegOp, V.Int i -> V.Int (Int32.neg i)
    | NegOp, V.Float z -> V.Float (-.z)
    | NotOp, V.Bool b -> V.Bool (not b)
    | _ -> crash e.at "runtime type error at unary operator"
    )

  | BinE (e1, AndOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool false -> V.Bool false
    | V.Bool true -> eval_exp env e2
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | BinE (e1, OrOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool false -> eval_exp env e2
    | V.Bool true -> V.Bool true
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | BinE (e1, op, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match op, v1, v2 with
    | AddOp, V.Int i1, V.Int i2 -> V.Int (Int32.add i1 i2)
    | SubOp, V.Int i1, V.Int i2 -> V.Int (Int32.sub i1 i2)
    | MulOp, V.Int i1, V.Int i2 -> V.Int (Int32.mul i1 i2)
    | DivOp, V.Int i1, V.Int i2 -> V.Int (Int32.div i1 i2)
    | ModOp, V.Int i1, V.Int i2 -> V.Int (Int32.rem i1 i2)
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
    | EqOp -> V.Bool (V.eq v1 v2)
    | NeOp -> V.Bool (not (V.eq v1 v2))
    | LtOp -> V.Bool (v1 < v2)
    | GtOp -> V.Bool (v1 > v2)
    | LeOp -> V.Bool (v1 <= v2)
    | GeOp -> V.Bool (v1 >= v2)
    )

  | TupE es ->
    let vs = List.map (eval_exp env) es in
    V.Tup vs

  | ProjE (e1, n) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Tup vs when n < List.length vs -> List.nth vs n
    | _ -> crash e.at "runtime type error at tuple access"
    )

  | ArrayE es ->
    let vs = List.map (eval_exp env) es in
    V.Array (List.map ref vs)

  | IdxE (e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1, v2 with
    | V.Null, _ -> trap e1.at "null reference at array access"
    | V.Array vs, V.Int i when 0l <= i && i < Int32.of_int (List.length vs) ->
      !(List.nth vs (Int32.to_int i))
    | V.Array vs, V.Int i -> trap e.at "array index out of bounds"
    | V.Text t, V.Int i when 0l <= i && i < Int32.of_int (String.length t) ->
      V.Byte t.[Int32.to_int i]
    | V.Text t, V.Int i -> trap e.at "text index out of bounds"
    | _ -> crash e.at "runtime type error at array access"
    )

  | CallE (e1, ts, es) ->
    let v1 = eval_exp env e1 in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap e1.at "null reference at function call"
    | V.Func f -> f (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at function call"
    )

  | NewE (x, ts, es) ->
    let v1 = eval_var env x in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap x.at "null reference at class instantiation"
    | V.Class f -> f (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at class instantiation"
    )

  | NewArrayE (_t, e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1 with
    | V.Int i -> V.Array (List.init (Int32.to_int i) (fun _ -> ref v2))
    | _ -> crash e.at "runtime type error at array instantiation"
    )

  | DotE (e1, x) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> trap e1.at "null reference at object access"
    | V.Obj (_, obj) ->
      (try !(E.Map.find x.it obj) with _ -> crash e.at "unknown field `%s`" x.it)
    | _ -> crash e.at "runtime type error at object access"
    )

  | AssignE (e1, e2) ->
    let r1 = eval_exp_ref env e1 in
    let v2 = eval_exp env e2 in
    r1 := v2;
    V.Tup []

  | AnnotE (e1, _t) ->
    eval_exp env e1

  | CastE (e1, t) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> V.Null
    | V.Obj (t', _) when T.sub t' (eval_typ env t) -> v1
    | V.Obj _ -> V.Null
    | _ -> crash e.at "runtime type error at cast"
    )

  | AssertE e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> V.Tup []
    | V.Bool false -> trap e.at "assertion failure"
    | _ -> crash e.at "runtime type error at conditional"
    )

  | IfE (e1, e2, e3) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> eval_exp env e2
    | V.Bool false -> eval_exp env e3
    | _ -> crash e.at "runtime type error at conditional"
    )

  | WhileE (e1, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> ignore (eval_exp env e2); eval_exp env e
    | V.Bool false -> V.Tup []
    | _ -> crash e.at "runtime type error at loop"
    )

  | RetE es ->
    let vs = List.map (eval_exp env) es in
    raise (Return vs)

  | BlockE ds ->
    fst (eval_decs env ds (V.Tup []))


and eval_exp_ref env e : V.value ref =
  match e.it with
  | VarE x ->
    eval_var_ref env x

  | IdxE (e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1, v2 with
    | V.Null, _ -> trap e1.at "null reference at array access"
    | V.Array vs, V.Int i when 0l <= i && i < Wasm.Lib.List32.length vs ->
      Wasm.Lib.List32.nth vs i
    | V.Array vs, V.Int i -> trap e.at "array index out of bounds"
    | _ -> crash e.at "runtime type error at array access"
    )

  | DotE (e1, x) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> trap e1.at "null reference at object access"
    | V.Obj (_, obj) ->
      (try E.Map.find x.it obj with _ -> crash e.at "unknown field `%s`" x.it)
    | _ -> crash e.at "runtime type error at object access"
    )

  | _ -> crash e.at "runtime type error at assignment"


(* Declarations *)

and eval_dec env d : V.value * env =
  match d.it with
  | ExpD e ->
    let v = eval_exp env e in
    v, E.empty

  | LetD (x, e) ->
    let v = eval_exp env e in
    V.Tup [], E.singleton_val x.it v

  | VarD (x, e) ->
    let v = eval_exp env e in
    V.Tup [], E.singleton_val x.it v

  | TypD (y, ys, t) ->
    let ys' = List.map it ys in
    let con ts = eval_typ (E.extend_typs_gnd env ys' ts) t in
    V.Tup [], E.singleton_typ y.it con

  | FuncD (x, ys, xts, _ts, e) ->
    let ys' = List.map it ys in
    let xs' = List.map it (List.map fst xts) in
    let rec f ts vs =
      let env' = E.extend_val env x.it (V.Func f) in
      let env' = E.extend_typs_gnd env' ys' ts in
      let env' = E.extend_vals env' xs' vs in
      try eval_exp env' e with Return [v] -> v | Return vs -> V.Tup vs
    in
    V.Tup [], E.singleton_val x.it (V.Func f)

  | ClassD (x, ys, xts, sup_opt, ds) ->
    let ys' = List.map it ys in
    let xs' = List.map it (List.map fst xts) in
    let cls = T.gen_class x.it ys' in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x.it con in
    let t' =
      match sup_opt with
      | None -> T.Obj
      | Some (x2, ts2, _) ->
        let env'' = E.extend_typs_abs env' ys' in
        eval_typ env'' (VarT (x2, ts2) @@ x2.at)
    in
    cls.T.sup <- t';
    let rec f ts vs =
      (* TODO: handle `this` *)
      let env'' = E.extend_val env' x.it (V.Class f) in
      let env'' = E.extend_typs_gnd env'' ys' ts in
      let env'' = E.extend_vals env'' xs' vs in
      let obj', env''' =
        match sup_opt with
        | None -> E.Map.empty, env''
        | Some (x2, ts2, es2) ->
          match eval_exp env'' (NewE (x2, ts2, es2) @@ x2.at) with
          | V.Obj (_, obj') ->
            obj', E.Map.fold (fun x v env -> Env.extend_val env x v) obj' env''
          | _ -> crash x2.at "runtime type error at super class instantiation"
      in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x.it (V.Class f) in
      let env''' = E.extend_vals env''' xs' vs in
      let _, oenv = eval_decs env''' ds (V.Tup []) in
      let obj = E.Map.union (fun x v' v -> v' := !v; Some v) obj' oenv.E.vals in
      V.Obj (con ts, obj)
    in
    V.Tup [],
    E.adjoin (E.singleton_typ x.it con) (E.singleton_val x.it (V.Class f))

  | ImportD (xs, url) ->
    (* TODO *)
    crash d.at "imports not implemented yet"

and eval_decs env ds v : V.value * env =
  match ds with
  | [] -> v, E.empty
  | d::ds' ->
    let v', env' = eval_dec env d in
    let v'', env'' = eval_decs (E.adjoin env env') ds' v' in
    v'', E.adjoin env' env''


(* Programs *)

let eval_prog env (Prog ds) : V.value * env =
  eval_decs env ds (V.Tup [])
