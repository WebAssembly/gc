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

type env = (T.sort * V.value ref, T.con) Env.env

module E =
struct
  include Env
  let singleton_val x (s, v) = Env.singleton_val x (s, ref v)
  let extend_val env x (s, v) = Env.extend_val env x (s, ref v)
  let extend_val_let env x v = Env.extend_val env x (T.LetS, ref v)
  let extend_vals_let env xs vs = List.fold_left2 extend_val_let env xs vs
  let extend_typ_gnd env y t = extend_typ env y (fun _ -> t)
  let extend_typ_abs env y = extend_typ_gnd env y (T.var y.it)
  let extend_typs_gnd env ys ts = List.fold_left2 extend_typ_gnd env ys ts
  let extend_typs_abs env ys = List.fold_left extend_typ_abs env ys
end

type pass = Full | Pre | Post


(* Types *)

let eval_typ_var env y : T.con =
  match E.find_opt_typ y env with
  | Some c -> c.it
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
    let env' = E.extend_typs_abs env ys in
    T.Func (ys', List.map (eval_typ env') ts1, List.map (eval_typ env') ts2)


(* Expressions *)

let eval_var_ref env x : V.value ref =
  match E.find_opt_val x env with
  | Some sv -> snd sv.it
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
    | V.Class (_, f) -> f (List.map (eval_typ env) ts) vs
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
      (try !(snd (E.Map.find x.it !obj))
       with _ -> crash e.at "unknown field `%s`" x.it)
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
    fst (eval_block Full env ds)


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
      (try snd (E.Map.find x.it !obj)
       with _ -> crash e.at "unknown field `%s`" x.it)
    | _ -> crash e.at "runtime type error at object access"
    )

  | _ -> crash e.at "runtime type error at assignment"


(* Declarations *)

and eval_dec pass env d : V.value * env =
  let this x = DotE (VarE ("this" @@ d.at) @@ d.at, x) @@ d.at in
  match d.it with
  | ExpD e ->
    let v = if pass = Pre then V.Tup [] else eval_exp env e in
    v, E.empty

  | LetD (x, e) ->
    let v = if pass = Post then eval_exp env (this x) else eval_exp env e in
    V.Tup [], E.singleton_val x (T.LetS, v)

  | VarD (x, t, e) ->
    let t' = eval_typ env t in
    let v = if pass = Pre then V.default t' else eval_exp env e in
    V.Tup [], E.singleton_val x (T.VarS, v)

  | TypD (y, ys, t) ->
    let con ts = eval_typ (E.extend_typs_gnd env ys ts) t in
    V.Tup [], E.singleton_typ y con

  | FuncD (x, ys, xts, _ts, e) ->
    let xs = List.map fst xts in
    let rec f ts vs =
      let env' = E.extend_val env x (T.FuncS, V.Func f) in
      let env' = E.extend_typs_gnd env' ys ts in
      let env' = E.extend_vals_let env' xs vs in
      try eval_exp env' e with Return [v] -> v | Return vs -> V.Tup vs
    in
    V.Tup [], E.singleton_val x (T.FuncS, V.Func f)

  | ClassD (x, ys, xts, sup_opt, ds) ->
    let ys' = List.map it ys in
    let xs = List.map fst xts in
    let cls =
      if pass <> Post then T.gen_class x.it ys' else
      match eval_exp env (this x) with
      | V.Class (cls, _) -> cls
      | _ -> assert false
    in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x con in
    Option.iter (fun (x2, ts2, _) ->
      let env'' = E.extend_typs_abs env' ys in
      cls.T.sup <- eval_typ env'' (VarT (x2, ts2) @@ x2.at)
    ) sup_opt;
    let rec v_class = V.Class (cls, f)
    and f ts vs =
      let env'' = E.extend_val env' x (T.ClassS, v_class) in
      let env'' = E.extend_typs_gnd env'' ys ts in
      let env'' = E.extend_vals_let env'' xs vs in
      let obj, env''' =
        match sup_opt with
        | None -> ref E.Map.empty, env''
        | Some (x2, ts2, es2) ->
          match eval_exp env'' (NewE (x2, ts2, es2) @@ x2.at) with
          | V.Obj (_, obj') ->
            obj', E.Map.fold (fun x v env ->
              Env.extend_val env (x @@ x2.at) v) !obj' env''
          | v -> crash x2.at "runtime type error at super class instantiation, got %s"
             (V.to_string v)
      in
      let v_inst = V.Obj (con ts, obj) in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x (T.ClassS, v_class) in
      let env''' = E.extend_vals_let env''' xs vs in
      let env''' = E.extend_val_let env''' ("this" @@ x.at) v_inst in
      let _, oenv = eval_block Pre env''' ds in
      obj := E.fold_vals (fun x sv obj ->
        match E.Map.find_opt x obj with
        | None -> E.Map.add x sv.it obj
        | Some (s, v') -> v' := !(snd sv.it); obj
      ) oenv !obj;
      ignore (eval_block Post env''' ds);
      v_inst
    in
    V.Tup [],
    E.adjoin (E.singleton_typ x con) (E.singleton_val x (T.ClassS, v_class))

  | ImportD (_xs, _url) ->
    (* TODO *)
    crash d.at "imports not implemented yet"

and eval_decs pass env ds v : V.value * env =
  match ds with
  | [] -> v, E.empty
  | d::ds' ->
    let v', env1 = eval_dec pass env d in
    let env' =
      if pass <> Post then env1 else
      match !(snd (E.find_val ("this" @@ no_region) env).it) with
      | V.Obj (_, obj) ->
        E.mapi_vals (fun x sv ->
          let s, v' = E.Map.find x !obj in v' := !(snd sv.it); (s, v') @@ sv.at
        ) env1
      | _ -> assert false
    in
    let v'', env2 = eval_decs pass (E.adjoin env env') ds' v' in
    v'', E.adjoin env1 env2

and eval_block pass env ds : V.value * env =
  eval_decs pass env ds (V.Tup [])


(* Programs *)

let eval_prog env p : V.value * env =
  let Prog ds = p.it in
  eval_block Full env ds
