open Source
open Syntax

module T = Type


(* Error handling *)

exception Error of Source.region * string

let error at fmt = Printf.ksprintf (fun s -> raise (Error (at, s))) fmt


(* Environments *)

type env = (T.sort * T.typ, T.kind * T.con) Env.env

module E =
struct
  include Env
  let extend_val_let env x t = extend_val env x (T.LetS, t)
  let extend_vals_let env xs ts =
    extend_vals env xs (List.map (fun t -> (T.LetS, t)) ts)

  let extend_typ env y kc =
    match find_opt_typ y env with
    | None -> Env.extend_typ env y kc
    | Some kc ->
      error y.at "type binding for `%s` shadows previous binding at %s"
        y.it (Source.string_of_region kc.at)

  let extend_typ_gnd env y t = extend_typ env y (0, fun _ -> t)
  let extend_typ_abs env y = extend_typ_gnd env y (T.var y.it)
  let extend_typs_abs env ys = List.fold_left extend_typ_abs env ys

  let adjoin env1 env2 =
    fold_typs (fun y kc env -> extend_typ env (y @@ kc.at) kc.it) env2
      (fold_vals (fun x st env -> extend_val env (x @@ st.at) st.it) env2 env1)
end

type pass = Full | Pre | Post


(* Types *)

let check_mut env m : T.mut =
  match m.it with
  | MutT -> T.Mut
  | ConstT -> T.Const

let check_typ_var env y : T.kind * T.con =
  match E.find_opt_typ y env with
  | Some kc -> kc.it
  | None -> error y.at "unknown type identifier `%s`" y.it


let rec check_typ_boxed env t : T.typ =
  let t' = check_typ env t in
  if not (T.sub t' T.Boxed || !Flags.boxed) then
    error t.at "boxed type expected but got %s" (T.to_string t');
  t'

and check_typ env t : T.typ =
  let t' = check_typ' env t in
  assert (t.et = None || T.eq (Option.get t.et) t');
  t.et <- Some t';
  t'

and check_typ' env t : T.typ =
  match t.it with
  | VarT (y, ts) ->
    let k, c = check_typ_var env y in
    if List.length ts <> k then
      error t.at "wrong number of type arguments at type use";
    c (List.map (check_typ_boxed env) ts)
  | BoolT -> T.Bool
  | ByteT -> T.Byte
  | IntT -> T.Int
  | FloatT -> T.Float
  | TextT -> T.Text
  | ObjT -> T.Obj
  | BoxT t1 -> T.Box (check_typ env t1)
  | TupT ts -> T.Tup (List.map (check_typ env) ts)
  | ArrayT (t1, m) -> T.Array (check_typ env t1, check_mut env m)
  | FuncT (ys, ts1, t2) ->
    let ys' = List.map Source.it ys in
    let env' = E.extend_typs_abs env ys in
    T.Func (ys', List.map (check_typ env') ts1, check_typ env' t2)


(* Expressions *)

let check_var_sort env x : T.sort * T.typ =
  match E.find_opt_val x env with
  | Some st ->
    if fst st.it = T.ProhibitedS then
      error x.at "`%s` cannot be used here" x.it;
    st.it
  | None -> error x.at "unknown value identifier `%s`" x.it

let check_var env x : T.typ =
  snd (check_var_sort env x)


let check_lit _env lit : T.typ =
  match lit with
  | NullL -> T.Null
  | BoolL _ -> T.Bool
  | IntL _ -> T.Int
  | FloatL _ -> T.Float
  | TextL _ -> T.Text


let rec check_exp env e : T.typ =
(*
  assert (e.et = None);
*)
  let t = check_exp' env e in
  e.et <- Some t;
  t

and check_exp' env e : T.typ =
  match e.it with
  | VarE x ->
    check_var env x

  | LitE l ->
    check_lit env l

  | UnE (op, e1) ->
    let t1 = check_exp env e1 in
    (match op, t1 with
    | (PosOp | NegOp | InvOp), T.Int -> T.Int
    | (PosOp | NegOp), T.Float -> T.Float
    | NotOp, T.Bool -> T.Bool
    | _ ->
      error e.at "unary operator not defined for type %s"
        (T.to_string t1)
    )

  | BinE (e1, op, e2) ->
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    let t = try T.lub t1 t2 with Failure _ ->
      error e.at "binary operator applied to incompatible types %s and %s"
        (T.to_string t1) (T.to_string t2)
    in
    (match op, t with
    | (AddOp | SubOp | MulOp | DivOp | ModOp), T.Int
    | (AndOp | OrOp | XorOp | ShlOp | ShrOp), T.Int -> t
    | (AddOp | SubOp | MulOp | DivOp), T.Float -> t
    | AddOp, T.Text -> t
    | _ ->
      error e.at "binary operator not defined for types %s and %s"
        (T.to_string t1) (T.to_string t2)
    )

  | RelE (e1, op, e2) ->
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    let t = try T.lub t1 t2 with Failure _ ->
      error e.at "comparison operator applied to incompatible types %s and %s"
        (T.to_string t1) (T.to_string t2)
    in
    (match op, t with
    | (EqOp | NeOp),
      (T.Null | T.Bool | T.Text | T.Obj | T.Box _ | T.Array _ | T.Inst _)
    | (EqOp | NeOp | LtOp | GtOp | LeOp | GeOp), (T.Byte | T.Int | T.Float) ->
      T.Bool
    | _ ->
      error e.at "comparison operator not defined for types %s and %s"
        (T.to_string t1) (T.to_string t2)
    )

  | LogE (e1, op, e2) ->
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    let t = try T.lub t1 t2 with Failure _ ->
      error e.at "binary operator applied to incompatible types %s and %s"
        (T.to_string t1) (T.to_string t2)
    in
    if t <> T.Bool then
      error e.at "logical operator not defined for types %s and %s"
        (T.to_string t1) (T.to_string t2);
    t

  | BoxE e1 ->
    let t1 = check_exp env e1 in
    T.Box t1

  | UnboxE e1 ->
    let t1 = check_exp env e1 in
    (match t1 with
    | T.Box t -> t
    | _ -> error e.at "box type expected but got %s" (T.to_string t1)
    )

  | TupE es ->
    let ts = List.map (check_exp env) es in
    T.Tup ts

  | ProjE (e1, n) ->
    let t1 = check_exp env e1 in
    (match t1 with
    | T.Tup ts when n < List.length ts -> List.nth ts n
    | T.Tup _ -> error e.at "wrong number of tuple components"
    | _ -> error e.at "tuple type expected but got %s" (T.to_string t1)
    )

  | ArrayE es ->
    let ts = List.map (check_exp env) es in
    let t =
      try List.fold_left T.lub T.Bot ts with Failure _ ->
        error e.at "array has inconsistent element types"
    in
    T.Array (t, T.Mut)

  | LenE e1 ->
    let t1 = check_exp env e1 in
    (match t1 with
    | T.Text | T.Array _ -> T.Int
    | _ -> error e1.at "array or text type expected but got %s" (T.to_string t1)
    )

  | IdxE (e1, e2) ->
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    (match t1, t2 with
    | T.Text, T.Int -> T.Byte
    | T.Array (t, _), T.Int -> t
    | T.Array (t, _), _ ->
      error e2.at "integer type expected but got %s" (T.to_string t2)
    | _ -> error e1.at "array or text type expected but got %s" (T.to_string t1)
    )

  | CallE (e1, ts, es) ->
    let t1 = check_exp env e1 in
    let ts' = List.map (check_typ_boxed env) ts in
    (match t1 with
    | T.Func (ys, ts1, t2) ->
      if List.length ts' <> List.length ys then
        error e1.at "wrong number of type arguments at function call";
      if List.length es <> List.length ts1 then
        error e1.at "wrong number of arguments at function call";
      let s = T.typ_subst ys ts' in
      let ts1' = List.map (T.subst s) ts1 in
      let t2' = T.subst s t2 in
      List.iter2 (fun eI tI ->
        let tI' = check_exp env eI in
        if not (T.sub tI' tI) then
          error eI.at "function expects argument type %s but got %s"
            (T.to_string tI) (T.to_string tI')
      ) es ts1';
      t2'
    | _ -> error e1.at "function type expected but got %s" (T.to_string t1)
    )

  | NewE (x, ts, es) ->
    let t1 = check_var env x in
    let ts' = List.map (check_typ_boxed env) ts in
    (match t1 with
    | T.Class cls ->
      if List.length ts' <> List.length cls.T.tparams then
        error x.at "wrong number of type arguments at class instantiation";
      if List.length es <> List.length cls.T.vparams then
        error x.at "wrong number of arguments at class instantiation";
      let s = T.typ_subst cls.T.tparams ts' in
      let ts1' = List.map (T.subst s) cls.T.vparams in
      List.iter2 (fun eI tI ->
        let tI' = check_exp env eI in
        if not (T.sub tI' tI) then
          error eI.at "class expects argument type %s but got %s"
            (T.to_string tI) (T.to_string tI')
      ) es ts1';
      T.Inst (cls, ts')
    | _ -> error x.at "class type expected but got %s" (T.to_string t1)
    )

  | NewArrayE (t, e1, e2) ->
    let t' = check_typ env t in
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    if not (T.sub t1 T.Int) then
      error e1.at "integer type expected but got %s" (T.to_string t1);
    if not (T.sub t2 t') then
      error e2.at "array initialization expects argument type %s but got %s"
        (T.to_string t') (T.to_string t2);
    T.Array (t', T.Mut)

  | DotE (e1, x) ->
    let t1 = check_exp env e1 in
    (match t1 with
    | T.Inst (cls, ts) ->
      (match List.assoc_opt x.it cls.T.def with
      | Some (s, t) ->
        T.subst (T.typ_subst cls.T.tparams ts) t
      | None -> error e1.at "unknown field `%s`" x.it
      )
    | _ -> error e1.at "object type expected but got %s" (T.to_string t1)
    )

  | AssignE (e1, e2) ->
    let t1 = check_exp_ref env e1 in
    let t2 = check_exp env e2 in
    if not (T.sub t2 t1) then
      error e1.at "assigment expects type %s but got %s"
        (T.to_string t1) (T.to_string t2);
    T.Tup []

  | AnnotE (e1, t) ->
    let t1 = check_exp env e1 in
    let t2 = check_typ env t in
    if not (T.sub t1 t2) then
      error e1.at "annotation expects type %s but got %s"
        (T.to_string t2) (T.to_string t1);
    t2

  | CastE (e1, x, ts) ->
    let t1 = check_exp env e1 in
    let t2 =
      match check_var env x with
      | T.Class cls ->
        let ts' = List.map (check_typ_boxed env) ts in
        if List.length ts' <> List.length cls.T.tparams then
          error x.at "wrong number of type arguments at class instantiation";
        T.Inst (cls, ts')
      | _ -> error x.at "class type expected but got %s" (T.to_string t1)
    in
    if not (T.sub t1 T.Obj) then
      error e1.at "object type expected but got %s" (T.to_string t1);
    if not (T.sub t2 T.Obj) then
      error x.at "object type expected as cast target";
    t2

  | AssertE e1 ->
    let t1 = check_exp env e1 in
    if not (T.sub t1 T.Bool) then
      error e1.at "boolean type expected but got %s" (T.to_string t1);
    T.Tup []

  | IfE (e1, e2, e3) ->
    let t1 = check_exp env e1 in
    let t2 = check_exp env e2 in
    let t3 = check_exp env e3 in
    if not (T.sub t1 T.Bool) then
      error e1.at "boolean type expected but got %s" (T.to_string t1);
    let t = try T.lub t2 t3 with Failure _ ->
      error e.at "coniditional branches have incompatible types %s and %s"
        (T.to_string t2) (T.to_string t3)
    in t

  | WhileE (e1, e2) ->
    let t1 = check_exp env e1 in
    let _t2 = check_exp env e2 in
    if not (T.sub t1 T.Bool) then
      error e1.at "boolean type expected but got %s" (T.to_string t1);
    T.Tup []

  | RetE e ->
    let t = check_exp env e in
    (match E.find_opt_val ("return" @@ no_region) env with
    | None -> error e.at "misplaced return"
    | Some st ->
      let (_, t') = st.it in
      if not (T.sub t t') then
        error e.at "return expects type %s but got %s"
          (T.to_string t') (T.to_string t);
    );
    T.Bot

  | BlockE ds ->
    let t, env' = check_block env ds in
    let escape = E.Set.inter (T.free t) (E.dom_typ env') in
    Option.iter (fun y ->
      error (E.find_typ (y @@ no_region) env').at
        "class type `%s` escapes scope of its definition in block type %s"
        y (T.to_string t)
    ) (E.Set.min_elt_opt escape);
    t


and check_exp_ref env e : T.typ =
  let t = check_exp env e in
  (match e.it with
  | VarE x ->
    let s, _ = check_var_sort env x in
    if s <> T.VarS then
      error e.at "mutable variable expected"

  | IdxE (e1, _) ->
    (match e1.et with
    | Some (T.Array (_, T.Mut)) -> ()
    | _ -> error e.at "mutable array expected"
    )

  | DotE (e1, x) ->
    (match e1.et with
    | Some (T.Inst (cls, _)) ->
      let s, _ = List.assoc x.it cls.T.def in
      if s <> T.VarS then
        error x.at "mutable field expected"
    | _ -> error x.at "mutable field expected"
    )

  | _ -> error e.at "invalid assignment target"
  );
  t


(* Declarations *)

and check_typdec env d : env =
  match d.it with
  | ExpD _ | LetD _ | VarD _ | FuncD _ ->
    E.empty

  | TypD (y, ys, t) ->
    let ys' = List.map it ys in
    let env' = E.extend_typs_abs env ys in
    let t' = check_typ env' t in
    let con ts = T.subst (T.typ_subst ys' ts) t' in
    E.singleton_typ y (List.length ys, con)

  | ClassD (x, ys, xts, sup_opt, _ds) ->
    let k = List.length ys in
    let ys' = List.map it ys in
    let cls = T.gen_cls d x.it ys' in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x (k, con) in
    let env' = E.extend_typs_abs env' ys in
    Option.iter (fun {it = (x2, ts2, _); at; _} ->
      cls.T.sup <- check_typ env' (VarT (x2, ts2) @@ x2.at);
      let rec cyclic t_sup =
        match t_sup with
        | T.Inst (sup, _) -> sup.T.id = cls.T.id || cyclic sup.T.sup
        | _ -> false
      in
      if cyclic cls.T.sup then
        error at "superclass is cyclic";
    ) sup_opt;
    E.singleton_typ x (k, con)

and check_typdecs env ds : env =
  match ds with
  | [] -> E.empty
  | d::ds' ->
    let env1 = check_typdec env d in
    let env2 = check_typdecs (E.adjoin env env1) ds' in
    try E.disjoint_union env1 env2 with E.Clash x ->
      error d.at "duplicate definition for type `%s`" x


and check_dec pass env d : T.typ * env =
  assert (d.et = None || fst (Option.get d.et) = T.Tup []);
  let t_res, t_bind, env' = check_dec' pass env d in
  d.et <- Some (t_res, t_bind);
  t_res, env'

and check_dec' pass env d : T.typ * T.typ * env =
  match d.it with
  | ExpD e ->
    let t = if pass = Pre then T.Tup [] else check_exp env e in
    t, T.Bot, E.empty

  | LetD (x, e) ->
    let t = if pass = Post then Option.get e.et else check_exp env e in
    T.Tup [], t, E.singleton_val x (T.LetS, t)

  | VarD (x, t, e) ->
    let t' = check_typ env t in
    if pass <> Pre then begin
      let t'' = check_exp env e in
      if not (T.sub t'' t') then
        error e.at "variable declaration expects type %s but got %s"
          (T.to_string t') (T.to_string t'')
    end;
    T.Tup [], t', E.singleton_val x (T.VarS, t')

  | TypD (y, ys, t) ->
(*
    let ys' = List.map it ys in
    let env' = E.extend_typs_abs env ys in
    let t' = check_typ env' t in
    let con ts = T.subst (T.typ_subst ys' ts) t' in
    T.Tup [], T.Bot, E.singleton_typ y (List.length ys, con)
*)
    T.Tup [], T.Bot, E.empty

  | FuncD (x, ys, xts, t, e) ->
    let ys' = List.map it ys in
    let env' = E.extend_typs_abs env ys in
    let ts1 = List.map (check_typ env') (List.map snd xts) in
    let t2 = check_typ env' t in
    let t = T.Func (ys', ts1, t2) in
    if pass <> Pre then begin
      let env'' = E.extend_val env' x (T.FuncS, t) in
      let env'' = E.extend_vals_let env'' (List.map fst xts) ts1 in
      let env'' = E.extend_val_let env'' ("return" @@ d.at) t2 in
      let t' = check_exp env'' e in
      if not (T.sub t' t2) then
        error e.at "function expects return type %s but got %s"
          (T.to_string t2) (T.to_string t')
    end;
    T.Tup [], t, E.singleton_val x (T.FuncS, t)

  | ClassD (x, ys, xts, sup_opt, ds) ->
(*
    let k = List.length ys in
    let ys' = List.map it ys in
    let cls =
      if pass <> Post then T.gen_cls d x.it ys' else
      match check_exp env (DotE (VarE ("this" @@ d.at) @@ d.at, x) @@ d.at) with
      | T.Class cls -> cls
      | _ -> assert false
    in
    let con ts = T.Inst (cls, ts) in
    let env' = E.extend_typ env x (k, con) in
    let env' = E.extend_typs_abs env' ys in
*)
    let env' = E.extend_typs_abs env ys in
    let k, con = check_typ_var env x in
    let t_inst = con (List.map T.var (List.map it ys)) in
    let cls =
      match t_inst with
      | T.Inst (cls, _) -> cls
      | _ -> assert false
    in
    let ts1 = List.map (check_typ env') (List.map snd xts) in
    cls.T.vparams <- ts1;
    Option.iter (fun {it = (x2, ts2, _); _} ->
      cls.T.sup <- check_typ env' (VarT (x2, ts2) @@ x2.at)) sup_opt;
    let t = T.Class cls in
(*
    if pass <> Pre then begin
      let t_inst = con (List.map T.var ys') in
*)
      let xs1 = List.map fst xts in
      let env'' = E.extend_val env' x (T.ClassS, t) in
      let env'' = E.extend_vals_let env'' xs1 ts1 in
      let env'' = E.extend_val env'' ("this" @@ x.at) (T.ProhibitedS, t_inst) in
      let sup_obj, env''', subst =
        match sup_opt with
        | None -> [], env'', T.empty_subst
        | Some sup ->
          let (x2, ts2, es2) = sup.it in
          match check_exp env'' (NewE (x2, ts2, es2) @@ sup.at) with
          | T.Inst (cls, ts2') ->
            let subst = T.typ_subst cls.T.tparams ts2' in
            let def' =
              List.map (fun (x, (s, t)) -> (x, (s, T.subst subst t))) cls.T.def in
            sup.et <- Some cls;
            def',
            List.fold_left (fun env'' (x, (s, t)) ->
              let s' = if s = T.LetS then s else T.ProhibitedS in
              E.extend_val env'' (x @@ x2.at) (s', t)
            ) env'' def',
            subst
          | _ -> assert false
      in
      let tenv = check_typdecs env''' ds in
      let env''' = E.adjoin env''' tenv in
      (* Rebind local vars to shadow parent fields *)
      let env''' = E.extend_val env''' x (T.ClassS, t) in
      let env''' = E.extend_vals_let env''' xs1 ts1 in
      let env''' = E.extend_val env''' ("this" @@ x.at) (T.ProhibitedS, t_inst) in
      let _, oenv = check_decs Pre prohibit_nonlet env''' ds T.Bot in
      E.iter_vals (fun x {it = (s, t); at; _} ->
        (match List.assoc_opt x sup_obj with
        | None -> ()
        | Some (s', t') ->
          if s' <> T.FuncS then
            error at "overriding superclass member `%s` that is not a function" x;
          if s <> T.FuncS then
            error at "overriding superclass function `%s` with a non-function" x;
          if not (T.sub t (T.subst subst t')) then
            error at "overriding superclass function `%s` of type %s with incompatible type %s"
              x (T.to_string t') (T.to_string t)
        )
      ) oenv;
      let obj = List.map (fun (x, st) -> (x, st.it)) (E.sorted_vals oenv) in
      cls.T.def <- sup_obj @ obj;
if pass <> Pre then begin
      (* Rebind unprohibited *)
      let env'''' = List.fold_left (fun env (x, (s, t)) ->
        E.extend_val env
          (x @@ (E.Map.find x env'''.E.vals).at) (s, t)) env''' sup_obj in
      (* Rebind local vars to shadow parent fields *)
      let env'''' = E.extend_val env'''' x (T.ClassS, t) in
      let env'''' = E.extend_vals_let env'''' xs1 ts1 in
      let env'''' = E.extend_val env'''' ("this" @@ x.at) (T.LetS, t_inst) in
      ignore (check_decs Post Fun.id env'''' ds T.Bot);
      E.iter_vals (fun x {it = (_, t); _} ->
        let escape = E.Set.inter (T.free t) (E.dom_typ oenv) in
        Option.iter (fun y ->
          error (E.find_typ (y @@ no_region) oenv).at
            "class type `%s` escapes scope of its definition with field %s : %s"
            y x (T.to_string t)
        ) (E.Set.min_elt_opt escape)
      ) oenv
    end;
    T.Tup [], t,
(*
    E.adjoin (E.singleton_typ x (k, con)) (E.singleton_val x (T.ClassS, t))
*)
    E.singleton_val x (T.ClassS, t)

and prohibit_nonlet env1 =
  E.map_vals (fun (s, t) -> (if s = T.LetS then s else T.ProhibitedS), t) env1

and check_decs pass prohibit env ds t : T.typ * env =
  match ds with
  | [] -> t, E.empty
  | d::ds' ->
    let t', env1 = check_dec pass env d in
    let env' = if pass <> Pre then env1 else prohibit env1 in
    let t'', env2 = check_decs pass prohibit (E.adjoin env env') ds' t' in
    try t'', E.disjoint_union env1 env2 with E.Clash x ->
      error d.at "duplicate definition for `%s`" x

and check_block env ds : T.typ * env =
  (* TODO: enable more general recursion among functions and classes *)
  let env1 = check_typdecs env ds in
  let t, env2 = check_recdecs (E.adjoin env env1) ds (T.Tup []) in
  t, E.adjoin env1 env2

and check_recdecs env ds t : T.typ * env =
  let t2, env1, env2 =
    match take_recgroup ds with
    | [], [] -> t, E.empty, E.empty
    | [], d::ds' ->
      let t1, env1 = check_decs Full Fun.id env [d] t in
      let t2, env2 = check_recdecs (E.adjoin env env1) ds' t1 in
      t2, env1, env2
    | ds1, ds' ->
      let _, env1 = check_decs Pre Fun.id env ds1 T.Bot in
      let t1, _ = check_decs Post Fun.id (E.adjoin env env1) ds1 t in
      let t2, env2 = check_recdecs (E.adjoin env env1) ds' t1 in
      t2, env1, env2
  in
  try t2, E.disjoint_union env1 env2 with E.Clash x ->
    let at =
      if E.Map.mem x env1.E.typs && E.Map.mem x env2.E.typs
      then (E.Map.find x env2.E.typs).at
      else (E.Map.find x env2.E.vals).at
    in error at "duplicate definition for `%s`" x

and take_recgroup ds : dec list * dec list =
  match ds with
  | ({it = FuncD _ | ClassD _ | TypD _; _} as d)::ds' ->
    let ds1, ds2 = take_recgroup ds' in d::ds1, ds2
  | _ -> [], ds


(* Programs *)

let get_env = ref (fun _at _url -> failwith "get_env")

let check_imp env env' d : env =
  let ImpD (xo, xs, url) = d.it in
  let menv = !get_env d.at url in
  let x = (match xo with None -> "" | Some x -> x.it) in
  let env', stats =
    List.fold_left (fun (env', stats) xI ->
      if not (E.mem_val xI menv || E.mem_typ xI menv) then
        error xI.at "unknown export `%s` in \"%s\"" xI.it url;
      let x' = (x ^ xI.it) @@ xI.at in
      (* TODO: technically, we have to selfify any class names here *)
      let env', sto =
        match E.find_opt_val xI menv with
        | None -> env', None
        | Some st -> E.extend_val env' x' st.it, Some st.it
      in
      let env', ko =
        match E.find_opt_typ xI menv with
        | None -> env', None
        | Some kc -> E.extend_typ env' x' kc.it, Some (fst kc.it)
      in
      env', (sto, ko)::stats
    ) (env', []) xs
  in
  d.et <- Some (List.rev stats);
  env'

let env0 =
  let at = Prelude.region in
  E.empty
  |> List.fold_right (fun (y, t) env ->
      E.extend_typ_gnd env (y @@ at) (check_typ env (t @@ at))
    ) Prelude.typs
  |> List.fold_right (fun (x, l) env ->
      E.extend_val_let env (x @@ at) (check_lit env l)
    ) Prelude.vals

let check_prog env p : T.typ * env =
  assert (p.et = None);
  let Prog (is, ds) = p.it in
  let env' = E.adjoin env0 env in
  let env1 = List.fold_left (check_imp env') E.empty is in
  let t, env2 = check_block (E.adjoin env' env1) ds in
  p.et <- Some t;
  t, Env.adjoin env1 env2
