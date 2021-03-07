module T = Type

exception Error of Source.region * string


(* Variables *)

type var = (string, unit) Source.phrase


(* Types *)

type typ = (typ', T.typ) Source.phrase
and typ' =
  | VarT of var * typ list
  | BoolT
  | ByteT
  | IntT
  | FloatT
  | TextT
  | ObjT
  | BoxT of typ
  | TupT of typ list
  | ArrayT of typ
  | FuncT of var list * typ list * typ


(* Expressions *)

type unop = PosOp | NegOp | InvOp | NotOp
type binop =
  | AddOp | SubOp | MulOp | DivOp | ModOp
  | AndOp | OrOp | XorOp | ShlOp | ShrOp | CatOp
type relop = EqOp | NeOp | LtOp | GtOp | LeOp | GeOp
type logop = AndThenOp | OrElseOp

type lit =
  | NullLit
  | BoolLit of bool
  | IntLit of int32
  | FloatLit of float
  | TextLit of string

type exp = (exp', T.typ) Source.phrase
and exp' =
  | VarE of var
  | LitE of lit
  | BoxE of exp
  | UnboxE of exp
  | UnE of unop * exp
  | BinE of exp * binop * exp
  | RelE of exp * relop * exp
  | LogE of exp * logop * exp
  | TupE of exp list
  | ProjE of exp * int
  | ArrayE of exp list
  | LenE of exp
  | IdxE of exp * exp
  | CallE of exp * typ list * exp list
  | NewE of var * typ list * exp list
  | NewArrayE of typ * exp * exp
  | DotE of exp * var
  | AssignE of exp * exp
  | AnnotE of exp * typ
  | CastE of exp * typ
  | BlockE of dec list
  | IfE of exp * exp * exp
  | WhileE of exp * exp
  | RetE of exp
  | AssertE of exp


(* Declarations *)

and dec = (dec', T.typ) Source.phrase
and dec' =
  | ExpD of exp
  | LetD of var * exp
  | VarD of var * typ * exp
  | TypD of var * var list * typ
  | FuncD of var * var list * (var * typ) list * typ * exp
  | ClassD of var * var list * (var * typ) list * (var * typ list * exp list) option * dec list


(* Modules *)

type imp = (imp', (T.sort * T.typ) option list) Source.phrase
and imp' =
  | ImpD of var option * var list * string

type prog = (prog', T.typ) Source.phrase
and prog' =
  | Prog of imp list * dec list
