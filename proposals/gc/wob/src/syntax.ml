exception Error of Source.region * string


(* Variables *)

type var = string Source.phrase


(* Types *)

type typ = typ' Source.phrase
and typ' =
  | VarT of var * typ list
  | NullT
  | BoolT
  | ByteT
  | IntT
  | FloatT
  | TextT
  | ObjT
  | TupT of typ list
  | ArrayT of typ
  | FuncT of var list * typ list * typ list


(* Expressions *)

type unop = PosOp | NegOp | NotOp
type binop = AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | CatOp
type relop = EqOp | NeOp | LtOp | GtOp | LeOp | GeOp

type lit =
  | NullLit
  | BoolLit of bool
  | IntLit of int32
  | FloatLit of float
  | TextLit of string

type exp = exp' Source.phrase
and exp' =
  | VarE of var
  | LitE of lit
  | UnE of unop * exp
  | BinE of exp * binop * exp
  | RelE of exp * relop * exp
  | TupE of exp list
  | ProjE of exp * int
  | ArrayE of exp list
  | IdxE of exp * exp
  | CallE of exp * typ list * exp list
  | NewE of exp * typ list * exp list
  | DotE of exp * var
  | AssignE of exp * exp
  | AnnotE of exp * typ
  | CastE of exp * typ
  | BlockE of dec list
  | IfE of exp * exp * exp
  | WhileE of exp * exp
  | RetE of exp list


(* Declarations *)

and dec = dec' Source.phrase
and dec' =
  | ExpD of exp
  | LetD of var * exp
  | VarD of var * exp
  | TypD of var * var list * typ
  | FuncD of var * var list * (var * typ) list * typ list * exp
  | ClassD of var * var list * (var * typ) list * (var * typ list * exp list) option * dec list
  | ImportD of var list * string


(* Modules *)

type prog =
  | Prog of dec list
