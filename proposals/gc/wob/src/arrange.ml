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

let rec typ t = match t.it with
  | VarT (x, ts) -> "VarT" $$ [var x] @ list typ ts
  | NullT -> Atom "NullT"
  | ByteT -> Atom "ByteT"
  | BoolT -> Atom "BoolT"
  | IntT -> Atom "IntT"
  | FloatT -> Atom "FloatT"
  | TextT -> Atom "TextT"
  | ObjT -> Atom "ObjT"
  | TupT ts -> "TupT" $$ list typ ts
  | ArrayT t -> "ArrayT" $$ [typ t]
  | FuncT (xs, ts1, ts2) ->
    "FuncT" $$ list var xs @ ["param" $$ list typ ts1; "result" $$ list typ ts2]


(* Expressions *)

let unop = function
  | PosOp -> "PosOp"
  | NegOp -> "NegOp"
  | NotOp -> "NotOp"

let binop = function
  | AddOp -> "AddOp"
  | SubOp -> "SubOp"
  | MulOp -> "MulOp"
  | DivOp -> "DivOp"
  | ModOp -> "ModOp"
  | AndOp -> "AndOp"
  | OrOp  -> "OrOp"
  | CatOp -> "CatOp"

let relop = function
  | EqOp -> "EqOp"
  | NeOp -> "NeOp"
  | LtOp -> "LtOp"
  | GtOp -> "GtOp"
  | LeOp -> "LeOp"
  | GeOp -> "GeOp"


let lit = function
  | NullLit -> Atom "NullLit"
  | BoolLit b -> "BoolLit" $$ [Atom (string_of_bool b)]
  | IntLit i -> "IntLit" $$ [Atom (Int32.to_string i)]
  | FloatLit z -> "FloatLit" $$ [Atom (string_of_float z)]
  | TextLit t -> "TextLit" $$ [Atom (string t)]

let rec exp e = match e.it with
  | VarE x -> "VarE" $$ [var x]
  | LitE l -> "LitE" $$ [lit l]
  | UnE (op, e1) -> "UnE" $$ [Atom (unop op); exp e1]
  | BinE (e1, op, e2) -> "BinE" $$ [exp e1; Atom (binop op); exp e2]
  | RelE (e1, op, e2) -> "RelE" $$ [exp e1; Atom (relop op); exp e2]
  | TupE es -> "TupE" $$ list exp es
  | ProjE (e1, i) -> "ProjE" $$ [exp e1; Atom (string_of_int i)]
  | ArrayE es -> "ArrayE" $$ list exp es
  | IdxE (e1, e2) -> "IdxE" $$ [exp e1; exp e2]
  | CallE (e1, ts, es) -> "CallE" $$ [exp e1] @ list typ ts @ list exp es
  | NewE (e1, ts, es) -> "NewE" $$ [exp e1] @ list typ ts @ list exp es
  | DotE (e1, x) -> "DotE" $$ [exp e1; var x]
  | AssignE (e1, e2) -> "AssignE" $$ [exp e1; exp e2]
  | AnnotE (e1, t) -> "AnnotE"  $$ [exp e1; typ t]
  | CastE (e1, t) -> "CastE"  $$ [exp e1; typ t]
  | BlockE ds -> "BlockE" $$ list dec ds
  | IfE (e1, e2, e3) -> "IfE" $$ [exp e1; exp e2; exp e3]
  | WhileE (e1, e2) -> "WhileE" $$ [exp e1; exp e2]
  | RetE es -> "RetE" $$ list exp es


(* Declarations *)

and dec d = match d.it with
  | ExpD e -> "ExpD" $$ [exp e]
  | LetD (x, e) -> "LetD" $$ [var x; exp e]
  | VarD (x, e) -> "VarD" $$ [var x; exp e]
  | TypD (x, xs, t) -> "TypD" $$ [var x] @ list var xs @ [typ t]
  | FuncD (x, xs, ps, ts, e) ->
    "FuncD" $$ [var x] @ ["gen" $$ list var xs] @
      ["param" $$ flatlist (fun (x, t) -> [var x; typ t]) ps] @
      list typ ts @ [exp e]
  | ClassD (x, xs, ps, so, ds) ->
    "ClassD" $$ [var x] @ ["gen" $$ list var xs] @
      ["param" $$ flatlist (fun (x, t) -> [var x; typ t]) ps] @
      opt (fun (x, ts, es) -> "sub" $$ [var x] @ list typ ts @ list exp es) so @
      list dec ds
  | ImportD (xs, url) -> "ImportD" $$ list var xs @ [Atom (string url)]


(* Modules *)

let prog m = match m with
  | Prog ds -> "Prog" $$ list dec ds
