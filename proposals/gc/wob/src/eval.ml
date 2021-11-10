open Source
open Syntax

module T = Type
module V = Value


(* Error handling *)

exception Trap of Source.region * string
exception Crash of Source.region * string
exception Return of V.value

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

  let to_vals env =
    fold_vals (fun x {it = (s, v); _} xvs -> Map.add x (s, !v) xvs) env Map.empty
  let of_vals xvs at =
    Map.fold (fun x sv env -> extend_val env (x @@ at) sv) xvs empty
end

type pass = Full | Pre | Post


(* Types *)

let eval_mut env m : T.mut =
  match m.it with
  | MutT -> T.Mut
  | ConstT -> T.Const

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
  | BoxT t1 -> T.Box (eval_typ env t1)
  | TupT ts -> T.Tup (List.map (eval_typ env) ts)
  | ArrayT (t1, m) -> T.Array (eval_typ env t1, eval_mut env m)
  | FuncT (ys, ts1, t2) ->
    let ys' = List.map Source.it ys in
    let env' = E.extend_typs_abs env ys in
    T.Func (ys', List.map (eval_typ env') ts1, eval_typ env' t2)


(* Expressions *)

let eval_var_ref env x : V.value ref =
  match E.find_opt_val x env with
  | Some sv -> snd sv.it
  | None -> crash x.at "unknown value identifier `%s`" x.it

let eval_var env x : V.value =
  !(eval_var_ref env x)

let eval_lit _env lit : V.value =
  match lit with
  | NullL -> V.Null
  | BoolL b -> V.Bool b
  | IntL i -> V.Int i
  | FloatL z -> V.Float z
  | TextL t -> V.Text t


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
    | InvOp, V.Int i -> V.Int (Int32.lognot i)
    | NotOp, V.Bool b -> V.Bool (not b)
    | _ -> crash e.at "runtime type error at unary operator"
    )

  | BinE (e1, op, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match op, v1, v2 with
    | AddOp, V.Int i1, V.Int i2 -> V.Int (Int32.add i1 i2)
    | SubOp, V.Int i1, V.Int i2 -> V.Int (Int32.sub i1 i2)
    | MulOp, V.Int i1, V.Int i2 -> V.Int (Int32.mul i1 i2)
    | DivOp, V.Int i1, V.Int i2 ->
      if i2 = 0l then trap e.at "division by zero" else
      V.Int (Int32.div i1 i2)
    | ModOp, V.Int i1, V.Int i2 ->
      if i2 = 0l then trap e.at "modulo by zero" else
      V.Int (Int32.rem i1 i2)
    | AndOp, V.Int i1, V.Int i2 -> V.Int (Int32.logand i1 i2)
    | OrOp,  V.Int i1, V.Int i2 -> V.Int (Int32.logor i1 i2)
    | XorOp, V.Int i1, V.Int i2 -> V.Int (Int32.logxor i1 i2)
    | ShlOp, V.Int i1, V.Int i2 ->
      V.Int Int32.(shift_left i1 (to_int i2 land 0x1f))
    | ShrOp, V.Int i1, V.Int i2 ->
      V.Int Int32.(shift_right i1 (to_int i2 land 0x1f))
    | AddOp, V.Float z1, V.Float z2 -> V.Float (z1 +. z2)
    | SubOp, V.Float z1, V.Float z2 -> V.Float (z1 -. z2)
    | MulOp, V.Float z1, V.Float z2 -> V.Float (z1 *. z2)
    | DivOp, V.Float z1, V.Float z2 -> V.Float (z1 /. z2)
    | AddOp, V.Text t1, V.Text t2 -> V.Text (t1 ^ t2)
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

  | LogE (e1, AndThenOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool false -> V.Bool false
    | V.Bool true -> eval_exp env e2
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | LogE (e1, OrElseOp, e2) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool false -> eval_exp env e2
    | V.Bool true -> V.Bool true
    | _ -> crash e.at "runtime type error at binary operator"
    )

  | BoxE e1 ->
    let v1 = eval_exp env e1 in
    V.Box v1

  | UnboxE e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Box v -> v
    | _ -> crash e.at "runtime type error at unboxing"
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

  | LenE e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> trap e1.at "null reference at length operation"
    | V.Array vs -> V.Int (Int32.of_int (List.length vs))
    | V.Text t -> V.Int (Int32.of_int (String.length t))
    | _ -> crash e.at "runtime type error at length operation"
    )

  | IdxE (e1, e2) ->
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in
    (match v1, v2 with
    | V.Null, _ -> trap e1.at "null reference at indexing operation"
    | V.Array vs, V.Int i when 0l <= i && i < Int32.of_int (List.length vs) ->
      !(List.nth vs (Int32.to_int i))
    | V.Array vs, V.Int i -> trap e.at "array index %ld out of bounds" i
    | V.Text t, V.Int i when 0l <= i && i < Int32.of_int (String.length t) ->
      V.Byte t.[Int32.to_int i]
    | V.Text t, V.Int i -> trap e.at "text index %ld out of bounds" i
    | _ -> crash e.at "runtime type error at indexing operation"
    )

  | CallE (e1, ts, es) ->
    let v1 = eval_exp env e1 in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap e1.at "null reference at function call"
    | V.Func f -> f E.Map.empty (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at function call"
    )

  | NewE (x, ts, es) ->
    let v1 = eval_var env x in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap x.at "null reference at class instantiation"
    | V.Class (_, f, _) -> f E.Map.empty (List.map (eval_typ env) ts) vs
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

  | CastE (e1, x, ts) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> V.Null
    | V.Obj (t', _) when T.sub t' (eval_typ env (VarT (x, ts) @@ e.at)) -> v1
    | V.Obj _ -> V.Null
    | _ -> crash e.at "runtime type error at cast"
    )

  | AssertE e1 ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Bool true -> V.Tup []
    | V.Bool false -> trap e.at "assertion failure"
    | _ -> crash e.at "runtime type error at assertion"
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

  | RetE e ->
    let v = eval_exp env e in
    raise (Return v)

  | BlockE ds ->
    fst (eval_block env ds)


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

and local x = VarE x @@ x.at
and this x = DotE (VarE ("this" @@ x.at) @@ x.at, x) @@ x.at

and eval_dec pass local env d : V.value * env =
  match d.it with
  | ExpD e ->
    let v = if pass = Pre then V.Tup [] else eval_exp env e in
    v, E.empty

  | LetD (x, e) ->
    let v = if pass = Post then eval_exp env (local x) else eval_exp env e in
    V.Tup [], E.singleton_val x (T.LetS, v)

  | VarD (x, t, e) ->
    let t' = eval_typ env t in
    let v = if pass = Pre then V.default t' else eval_exp env e in
    V.Tup [], E.singleton_val x (T.VarS, v)

  | TypD (y, ys, t) ->
    let con ts = eval_typ (E.extend_typs_gnd env ys ts) t in
    V.Tup [], E.singleton_typ y con

  | FuncD (x, ys, xts, _t, e) ->
    let xs = List.map fst xts in
    let rec f envR ts vs =
      let envR' = E.Map.map (fun (s, v) -> s, V.fix envR v) envR in
      let env' = E.adjoin env (E.of_vals envR' d.at) in
      let env' = E.extend_val env' x (T.FuncS, V.fix envR (V.Func f)) in
      let env' = E.extend_typs_gnd env' ys ts in
      let env' = E.extend_vals_let env' xs vs in
      try eval_exp env' e with Return v -> v
    in
    let v = if pass = Post then eval_exp env (local x) else V.Func f in
    V.Tup [], E.singleton_val x (T.FuncS, v)

  | ClassD (x, ys, xts, sup_opt, ds) ->
    let ys' = List.map it ys in
    let xs = List.map fst xts in
    let cls =
      if pass <> Post then T.gen_cls d x.it ys' else
      match eval_exp env (local x) with
      | V.Class (cls, _, _) -> cls
      | _ -> assert false
    in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x con in
    Option.iter (fun {it = (x2, ts2, _); _} ->
      let env'' = E.extend_typs_abs env' ys in
      cls.T.sup <- eval_typ env'' (VarT (x2, ts2) @@ x2.at)
    ) sup_opt;
    let rec v_class = V.Class (cls, inst, alloc)
    and inst envR ts vs =
      let v_inst, init = alloc envR (con ts) ts vs in
      init (); v_inst
    and alloc envR t_inst ts vs =
      let envR' = E.Map.map (fun (s, v) -> s, V.fix envR v) envR in
      let env'' = E.adjoin env' (E.of_vals envR' d.at) in
      let env'' = E.extend_val env'' x (T.ClassS, V.fix envR v_class) in
      let env'' = E.extend_typs_gnd env'' ys ts in
      let env'' = E.extend_vals_let env'' xs vs in
      let v_inst, init', env''' =
        match sup_opt with
        | None -> V.Obj (t_inst, ref E.Map.empty), (fun () -> ()), env''
        | Some {it = (x2, ts2, es2); _} ->
          let v2 = eval_var env'' x2 in
          let ts2' = List.map (eval_typ env'') ts2 in
          let vs2 = List.map (eval_exp env'') es2 in
          (match v2 with
          | V.Null -> trap x2.at "null reference at class instantiation"
          | V.Class (_, _, alloc') ->
            let v_inst, init' = alloc' E.Map.empty t_inst ts2' vs2 in
            v_inst, init', E.Map.fold (fun x v env ->
              Env.extend_val env (x @@ x2.at) v) !(V.as_obj v_inst) env''
          | _ -> crash x2.at "runtime type error at class instantiation"
          )
      in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x (T.ClassS, v_class) in
      let env''' = E.extend_vals_let env''' xs vs in
      let env''' = E.extend_val_let env''' ("this" @@ x.at) v_inst in
      let _, oenv = eval_decs Pre this Fun.id env''' ds V.Null in
      let obj = V.as_obj v_inst in
      obj := E.fold_vals (fun x sv obj ->
        match E.Map.find_opt x obj with
        | None -> E.Map.add x sv.it obj
        | Some (s, v') -> v' := !(snd sv.it); obj
      ) oenv !obj;
      v_inst,
      fun () ->
        init' ();
        ignore (eval_decs Post this (init_fields env''') env''' ds V.Null)
    in
    V.Tup [],
    E.adjoin (E.singleton_typ x con) (E.singleton_val x (T.ClassS, v_class))

and init_fields env env1 : env =
  let obj =
    match !(snd (E.find_val ("this" @@ no_region) env).it) with
    | V.Obj (_, obj) -> obj
    | _ -> assert false
  in
  E.mapi_vals (fun x (s, v) ->
    let s, v' = E.Map.find x !obj in v' := !v; (s, v')
  ) env1

and eval_decs pass local init env ds v : V.value * env =
  match ds with
  | [] -> v, E.empty
  | d::ds' ->
    let v', env1 = eval_dec pass local env d in
    let env' = if pass <> Post then env1 else init env1 in
    let v'', env2 = eval_decs pass local init (E.adjoin env env') ds' v' in
    v'', E.adjoin env1 env2

and eval_block env ds : V.value * env =
  (* TODO: enable more general recursion among functions and classes *)
  eval_recdecs env ds (V.Tup [])

and eval_recdecs env ds v : V.value * env =
  match take_recgroup ds with
  | [], [] -> v, E.empty
  | [], d::ds' ->
    let v', env1 = eval_decs Full local Fun.id env [d] v in
    let v'', env2 = eval_recdecs (E.adjoin env env1) ds' v' in
    v'', E.adjoin env1 env2
  | ds1, ds' ->
    let _, env1 = eval_decs Pre local Fun.id env ds1 V.Null in
    let v', env1' = eval_decs Post local Fun.id (E.adjoin env env1) ds1 v in
    let envR = E.to_vals env1' in
    let env1'' = E.map_vals (fun (s, v) -> s, ref (V.fix envR !v)) env1' in
    let v'', env2 = eval_recdecs (E.adjoin env env1'') ds' v' in
    v'', E.adjoin env1'' env2

and take_recgroup ds : dec list * dec list =
  match ds with
  | ({it = FuncD _ | ClassD _ | TypD _; _} as d)::ds' ->
    let ds1, ds2 = take_recgroup ds' in d::ds1, ds2
  | _ -> [], ds


(* Programs *)

let get_env = ref (fun _at _url -> failwith "get_env")

let eval_imp env env' d : env =
  let ImpD (xo, xs, url) = d.it in
  let menv = !get_env d.at url in
  let x = (match xo with None -> "" | Some x -> x.it) in
  List.fold_left (fun env' xI ->
    let x' = (x ^ xI.it) @@ xI.at in
    let env' =
      match E.find_opt_val xI menv with
      | None -> env'
      | Some sv -> Env.extend_val env' x' sv.it
    in
    let env' =
      match E.find_opt_typ xI menv with
      | None -> env'
      | Some c -> E.extend_typ env' x' c.it
    in
    env'
  ) env' xs

let env0 =
  let at = Prelude.region in
  E.empty
  |> List.fold_right (fun (y, t) env ->
      E.extend_typ_gnd env (y @@ at) (eval_typ env (t @@ at))
    ) Prelude.typs
  |> List.fold_right (fun (x, l) env ->
      E.extend_val_let env (x @@ at) (eval_lit env l)
    ) Prelude.vals

let eval_prog env p : V.value * env =
  let Prog (is, ds) = p.it in
  let env' = Env.adjoin env0 env in
  let env1 = List.fold_left (eval_imp env') E.empty is in
  let v, env2 = eval_block (E.adjoin env' env1) ds in
  v, E.adjoin env1 env2
