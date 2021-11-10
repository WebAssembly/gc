open Source
open Syntax
open Wasm.Sexpr


(* Helpers *)

let ($$) head inner = Node (head, inner)

let string s = "\"" ^ String.escaped s ^ "\""
let list = List.map
let flatlist = List.concat_map
let opt f xo = list f (Option.to_list xo)


(* Variables *)

let var x = Atom x.it


(* Types *)

let mut m = match m.it with
  | MutT -> Atom "Mut"
  | ConstT -> Atom "Const"

let rec typ t = match t.it with
  | VarT (y, ts) -> "VarT" $$ [var y] @ list typ ts
  | BoolT -> Atom "BoolT"
  | ByteT -> Atom "ByteT"
  | IntT -> Atom "IntT"
  | FloatT -> Atom "FloatT"
  | TextT -> Atom "TextT"
  | ObjT -> Atom "ObjT"
  | BoxT t -> "BoxT" $$ [typ t]
  | TupT ts -> "TupT" $$ list typ ts
  | ArrayT (t, m) -> "ArrayT" $$ [typ t; mut m]
  | FuncT (ys, ts1, t2) ->
    "FuncT" $$ list var ys @ ["param" $$ list typ ts1; typ t2]


(* Expressions *)

let unop = function
  | PosOp -> "PosOp"
  | NegOp -> "NegOp"
  | InvOp -> "InvOp"
  | NotOp -> "NotOp"

let binop = function
  | AddOp -> "AddOp"
  | SubOp -> "SubOp"
  | MulOp -> "MulOp"
  | DivOp -> "DivOp"
  | ModOp -> "ModOp"
  | AndOp -> "AndOp"
  | OrOp  -> "OrOp"
  | XorOp -> "XorOp"
  | ShlOp -> "ShlOp"
  | ShrOp -> "ShrOp"

let relop = function
  | EqOp -> "EqOp"
  | NeOp -> "NeOp"
  | LtOp -> "LtOp"
  | GtOp -> "GtOp"
  | LeOp -> "LeOp"
  | GeOp -> "GeOp"

let logop = function
  | AndThenOp -> "AndThenOp"
  | OrElseOp  -> "OrElseOp"


let lit = function
  | NullL -> Atom "NullL"
  | BoolL b -> "BoolL" $$ [Atom (string_of_bool b)]
  | IntL i -> "IntL" $$ [Atom (Int32.to_string i)]
  | FloatL z -> "FloatL" $$ [Atom (string_of_float z)]
  | TextL t -> "TextL" $$ [Atom (string t)]

let rec exp e = match e.it with
  | VarE x -> "VarE" $$ [var x]
  | LitE l -> "LitE" $$ [lit l]
  | BoxE e1 -> "BoxE" $$ [exp e1]
  | UnboxE e1 -> "UnboxE" $$ [exp e1]
  | UnE (op, e1) -> "UnE" $$ [Atom (unop op); exp e1]
  | BinE (e1, op, e2) -> "BinE" $$ [exp e1; Atom (binop op); exp e2]
  | RelE (e1, op, e2) -> "RelE" $$ [exp e1; Atom (relop op); exp e2]
  | LogE (e1, op, e2) -> "LogE" $$ [exp e1; Atom (logop op); exp e2]
  | TupE es -> "TupE" $$ list exp es
  | ProjE (e1, i) -> "ProjE" $$ [exp e1; Atom (string_of_int i)]
  | ArrayE es -> "ArrayE" $$ list exp es
  | LenE e1 -> "LenE" $$ [exp e1]
  | IdxE (e1, e2) -> "IdxE" $$ [exp e1; exp e2]
  | CallE (e1, ts, es) -> "CallE" $$ [exp e1] @ list typ ts @ list exp es
  | NewE (y, ts, es) -> "NewE" $$ [var y] @ list typ ts @ list exp es
  | NewArrayE (t, e1, e2) -> "NewArrayE" $$ [typ t; exp e1; exp e2]
  | DotE (e1, x) -> "DotE" $$ [exp e1; var x]
  | AssignE (e1, e2) -> "AssignE" $$ [exp e1; exp e2]
  | AnnotE (e1, t) -> "AnnotE"  $$ [exp e1; typ t]
  | CastE (e1, y, ts) -> "CastE"  $$ [exp e1; var y] @ list typ ts
  | AssertE e1 -> "AssertE" $$ [exp e1]
  | IfE (e1, e2, e3) -> "IfE" $$ [exp e1; exp e2; exp e3]
  | WhileE (e1, e2) -> "WhileE" $$ [exp e1; exp e2]
  | RetE e -> "RetE" $$ [exp e]
  | BlockE ds -> "BlockE" $$ list dec ds


(* Declarations *)

and dec d = match d.it with
  | ExpD e -> "ExpD" $$ [exp e]
  | LetD (x, e) -> "LetD" $$ [var x; exp e]
  | VarD (x, t, e) -> "VarD" $$ [var x; typ t; exp e]
  | TypD (y, ys, t) -> "TypD" $$ [var y] @ list var ys @ [typ t]
  | FuncD (x, ys, xts, t, e) ->
    "FuncD" $$ [var x] @ ["gen" $$ list var ys] @
      ["param" $$ flatlist (fun (x, t) -> [var x; typ t]) xts] @
      [typ t; exp e]
  | ClassD (x, ys, xts, so, ds) ->
    "ClassD" $$ [var x] @ ["gen" $$ list var ys] @
      ["param" $$ flatlist (fun (x, t) -> [var x; typ t]) xts] @ opt sup so @
      list dec ds

and sup s = match s.it with
  | x, ts, es -> "sup" $$ [var x] @ list typ ts @ list exp es


(* Modules *)

let imp d = match d.it with
  | ImpD (xo, xs, url) ->
    "ImpD" $$ opt var xo @ list var xs @ [Atom (string url)]

let prog m = match m.it with
  | Prog (is, ds) -> "Prog" $$ list imp is @ list dec ds
