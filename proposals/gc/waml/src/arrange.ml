open Source
open Syntax
open Wasm.Sexpr


(* Helpers *)

let ($$) head inner = Node (head, inner)

let string s = "\"" ^ String.escaped s ^ "\""
let list = List.map
let flatlist = List.concat_map
let opt f xo = list f (Option.to_list xo)


(* Variables and Paths *)

let var x = Atom x.it

let rec path : 'a. 'a path -> sexpr =
  fun p -> match p.it with
  | PlainP x -> "PlainP" $$ [var x]
  | QualP (p, x) -> "QualP" $$ [path p; var x]


(* Types *)

let rec typ t = match t.it with
  | VarT y -> "VarT" $$ [var y]
  | ConT (q, ts) -> "ConT" $$ [path q] @ list typ ts
  | BoolT -> Atom "BoolT"
  | ByteT -> Atom "ByteT"
  | IntT -> Atom "IntT"
  | FloatT -> Atom "FloatT"
  | TextT -> Atom "TextT"
  | RefT t1 -> "RefT" $$ [typ t1]
  | TupT ts -> "TupT" $$ list typ ts
  | FunT (t1, t2) -> "FunT" $$ [typ t1; typ t2]
  | PackT s -> "PackT" $$ [sig_ s]


(* Patterns *)

and lit = function
  | BoolL b -> "BoolL" $$ [Atom (if b then "True" else "False")]
  | IntL i -> "IntL" $$ [Atom (Int32.to_string i)]
  | FloatL z -> "FloatL" $$ [Atom (string_of_float z)]
  | TextL t -> "TextL" $$ [Atom (string t)]

and pat p = match p.it with
  | WildP -> Atom "WildP"
  | VarP x -> "VarP" $$ [var x]
  | LitP l -> "LitP" $$ [lit l]
  | ConP (q, ps) -> "ConP" $$ [path q] @ list pat ps
  | RefP p1 -> "RefP" $$ [pat p1]
  | TupP ps -> "TupP" $$ list pat ps
  | AnnotP (p1, t) -> "AnnotP" $$ [pat p1; typ t]


(* Expressions *)

and unop = function
  | PosOp -> "PosOp"
  | NegOp -> "NegOp"
  | InvOp -> "InvOp"
  | NotOp -> "NotOp"

and binop = function
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
  | CatOp -> "CatOp"

and relop = function
  | EqOp -> "EqOp"
  | NeOp -> "NeOp"
  | LtOp -> "LtOp"
  | GtOp -> "GtOp"
  | LeOp -> "LeOp"
  | GeOp -> "GeOp"

and logop = function
  | AndThenOp -> "AndThenOp"
  | OrElseOp  -> "OrElseOp"


and exp e = match e.it with
  | VarE q -> "VarE" $$ [path q]
  | LitE l -> "LitE" $$ [lit l]
  | ConE q -> "ConE" $$ [path q]
  | UnE (op, e1) -> "UnE" $$ [Atom (unop op); exp e1]
  | BinE (e1, op, e2) -> "BinE" $$ [exp e1; Atom (binop op); exp e2]
  | RelE (e1, op, e2) -> "RelE" $$ [exp e1; Atom (relop op); exp e2]
  | LogE (e1, op, e2) -> "LogE" $$ [exp e1; Atom (logop op); exp e2]
  | RefE e1 -> "RefE" $$ [exp e1]
  | DerefE e1 -> "DerefE" $$ [exp e1]
  | AssignE (e1, e2) -> "AssignE" $$ [exp e1; exp e2]
  | TupE es -> "TupE" $$ list exp es
  | FunE (p1, e2) -> "FunE" $$ [pat p1; exp e2]
  | AppE (e1, e2) -> "AppE" $$ [exp e1; exp e2]
  | AnnotE (e1, t) -> "AnnotE"  $$ [exp e1; typ t]
  | IfE (e1, e2, e3) -> "IfE" $$ [exp e1; exp e2; exp e3]
  | CaseE (e1, pes) ->
    "CaseE" $$ [exp e1] @ ["case" $$ flatlist (fun (p, e) -> [pat p; exp e]) pes]
  | PackE (m, s) -> "PackE" $$ [mod_ m; sig_ s]
  | LetE (ds, e1) -> "LetE" $$ list dec ds @ [exp e1]


(* Declarations *)

and dec d = match d.it with
  | ExpD e -> "ExpD" $$ [exp e]
  | AssertD e -> "AssertD" $$ [exp e]
  | ValD (p, e) -> "ValD" $$ [pat p; exp e]
  | TypD (y, ys, t) -> "TypD" $$ [var y] @ list var ys @ [typ t]
  | DatD (y, ys, cs) ->
    "DatD" $$ [var y] @ list var ys @ ["con" $$ flatlist con cs]
  | ModD (x, m) -> "ModD" $$ [var x; mod_ m]
  | SigD (y, s) -> "SigD" $$ [var y; sig_ s]
  | RecD ds -> "RecD" $$ list dec ds
  | InclD m -> "InclD" $$ [mod_ m]

and con c = match c.it with
  | (x, ts) -> [var x] @ list typ ts


(* Signatures *)

and spec s = match s.it with
  | ValS (x, ys, t) -> "ValS" $$ list var ys @ [var x; typ t]
  | TypS (y, ys, to_) -> "TypS" $$ [var y] @ list var ys @ opt typ to_
  | DatS (y, ys, cs) ->
    "DatS" $$ [var y] @ list var ys @ ["con" $$ flatlist con cs]
  | ModS (x, s) -> "ModS" $$ [var x; sig_ s]
  | SigS (y, s) -> "SigS" $$ [var y; sig_ s]
  | RecS ss -> "RecS" $$ list spec ss
  | InclS s -> "InclS" $$ [sig_ s]

and sig_ s = match s.it with
  | ConS q -> "ConS" $$ [path q]
  | StrS ss -> "StrS" $$ list spec ss
  | FunS (x, s1, s2) -> "FunS" $$ [var x; sig_ s1; sig_ s2]
  | WithS (s1, q, ys, t) -> "WithS" $$ [sig_ s; path q] @ list var ys @ [typ t]


(* Modules *)

and mod_ m = match m.it with
  | VarM q -> "VarM" $$ [path q]
  | StrM ds -> "StrM" $$ list dec ds
  | FunM (x, s1, m2) -> "FunM" $$ [var x; sig_ s1; mod_ m2]
  | AppM (m1, m2) -> "AppM" $$ [mod_ m1; mod_ m2]
  | AnnotM (m1, s) -> "AnnotM"  $$ [mod_ m1; sig_ s]
  | UnpackM (e, s) -> "UnpackM" $$ [exp e; sig_ s]
  | LetM (ds, m1) -> "LetM" $$ list dec ds @ [mod_ m1]


(* Programs *)

let imp d = match d.it with
  | ImpD (x, url) ->
    "ImpD" $$ [var x; Atom (string url)]

let prog m = match m.it with
  | Prog (is, ds) -> "Prog" $$ list imp is @ list dec ds
