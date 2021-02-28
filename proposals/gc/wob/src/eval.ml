open Source
open Syntax

module V = Value


(* Error handling *)

exception Trap of Source.region * string
exception Crash of Source.region * string
exception Return of V.value list

let trap at fmt = Printf.ksprintf (fun s -> raise (Trap (at, s))) fmt
let crash at fmt = Printf.ksprintf (fun s -> raise (Crash (at, s))) fmt

let lookup_val env x =
  match V.lookup_val env x with
  | Some v -> v
  | None -> crash x.at "unknown value identifier %s" x.it

let lookup_typ env x =
  match V.lookup_typ env x with
  | Some c -> c
  | None -> crash x.at "unknown type identifier %s" x.it


(* Types *)

let typ_counter = ref 0

let gen_typ x =
  incr typ_counter;
  ("$" ^ x.it ^ "/" ^ string_of_int !typ_counter) @@ x.at

let is_gen_typ x =
  String.length x.it > 0 && x.it.[0] = '$'

let rec eval_typ env t =
  match t.it with
  | VarT (x, ts) when is_gen_typ x -> VarT (x, List.map (eval_typ env) ts) @@ t.at
  | VarT (x, ts) -> let c = lookup_typ env x in c (List.map (eval_typ env) ts)
  | NullT -> NullT @@ t.at
  | BoolT -> BoolT @@ t.at
  | ByteT -> ByteT @@ t.at
  | IntT -> IntT @@ t.at
  | FloatT -> FloatT @@ t.at
  | TextT -> TextT @@ t.at
  | ObjT -> ObjT @@ t.at
  | TupT ts -> TupT (List.map (eval_typ env) ts) @@ t.at
  | ArrayT t -> ArrayT (eval_typ env t) @@ t.at
  | FuncT (xs, ts1, ts2) ->
    let env' = List.fold_left V.extend_typ_abs env xs in
    FuncT (xs, List.map (eval_typ env') ts1, List.map (eval_typ env') ts2) @@ t.at


(* Expressions *)

let eval_lit lit : V.value =
  match lit with
  | NullLit -> V.Null
  | BoolLit b -> V.Bool b
  | IntLit i -> V.Int i
  | FloatLit z -> V.Float z
  | TextLit t -> V.Text t


let rec eval_exp env e : V.value =
  match e.it with
  | VarE x ->
    !(lookup_val env x)

  | LitE l ->
    eval_lit l

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
    | EqOp -> V.Bool (v1 = v2)
    | NeOp -> V.Bool (v1 <> v2)
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

  | NewE (e1, ts, es) ->
    let v1 = eval_exp env e1 in
    let vs = List.map (eval_exp env) es in
    (match v1 with
    | V.Null -> trap e1.at "null reference at class instantiation"
    | V.Class f -> f (List.map (eval_typ env) ts) vs
    | _ -> crash e.at "runtime type error at class instantiation"
    )

  | DotE (e1, x) ->
    let v1 = eval_exp env e1 in
    (match v1 with
    | V.Null -> trap e1.at "null reference at object access"
    | V.Obj (_, obj) -> !(lookup_val obj x)
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
    | V.Obj (t', _) when true (* TODO: Type.sub t' (eval_typ env t) *) -> v1
    | V.Obj _ -> V.Null
    | _ -> crash e.at "runtime type error at cast"
    )

  | BlockE ds ->
    fst (eval_decs env ds (V.Tup []))

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


and eval_exp_ref env e : V.value ref =
  match e.it with
  | VarE x ->
    lookup_val env x

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
    | V.Obj (_, obj) -> lookup_val obj x
    | _ -> crash e.at "runtime type error at object access"
    )

  | _ -> crash e.at "runtime type error at assignment"


(* Declarations *)

and eval_dec env d : V.value * V.env =
  match d.it with
  | ExpD e ->
    let v = eval_exp env e in
    v, V.empty_env

  | LetD (x, e) ->
    let v = eval_exp env e in
    v, V.val_env x v

  | VarD (x, e) ->
    let v = eval_exp env e in
    v, V.val_env x v

  | TypD (x, xs, t) ->
    let c ts =
      let env' = List.fold_left2 V.extend_typ_gnd env xs ts in
      eval_typ env' t
    in
    V.Tup [], V.typ_env x c

  | FuncD (x, xs, xts, _ts, e) ->
    let rec f ts vs =
      let env' = V.extend_val env x (V.Func f) in
      let env' = List.fold_left2 V.extend_typ_gnd env' xs ts in
      let env' = List.fold_left2 V.extend_val env' (List.map fst xts) vs in
      try eval_exp env' e with Return [v] -> v | Return vs -> V.Tup vs
    in
    let v = V.Func f in
    v, V.val_env x v

  | ClassD (x, xs, xts, supo, ds) ->
    let x' = gen_typ x in
    let c ts = VarT (x', ts) @@ x.at in
    let rec f ts vs =
      let env' = V.extend_typ env x c in
      let env' = V.extend_val env' x (V.Class f) in
      let env' = List.fold_left2 V.extend_typ_gnd env' xs ts in
      let env' = List.fold_left2 V.extend_val env' (List.map fst xts) vs in
      let env1 =
        match supo with
        | None -> V.empty_env
        | Some (x2, ts2, es2) ->
          let v2 = !(lookup_val env' x2) in
          let vs2 = List.map (eval_exp env') es2 in
          match v2 with
          | V.Class f' ->
            (match f' (List.map (eval_typ env') ts2) vs2 with
            | V.Obj (_, env'') -> env''
            | _ -> crash x2.at "runtime type error at super class instantiation"
            )
          | _ -> crash x2.at "runtime type error at super class instantiation"
      in
      let _, env2 = eval_decs env' ds (V.Tup []) in
      V.Obj (c ts, V.adjoin_env env1 env2)
    in
    let v = V.Class f in
    v, V.adjoin_env (V.typ_env x c) (V.val_env x v)

  | ImportD (xs, url) ->
    (* TODO *)
    crash d.at "imports not implemented yet"

and eval_decs env ds v : V.value * V.env =
  match ds with
  | [] -> v, V.empty_env
  | d::ds' ->
    let v', env' = eval_dec env d in
    let v'', env'' = eval_decs (V.adjoin_env env env') ds' v' in
    v'', V.adjoin_env env' env''


(* Programs *)

let eval_prog env (Prog ds) : V.value * V.env =
  eval_decs env ds (V.Tup [])
