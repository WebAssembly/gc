module T = Type

exception Error of Source.region * string


(* Variables and Paths *)

type var = (string, unit) Source.phrase

type path = (path', T.typ) Source.phrase
and path' =
  | PlainP of var
  | QualP of path * var


(* Types *)

type typ = (typ', T.typ) Source.phrase
and typ' =
  | VarT of var
  | ConT of path * typ list
  | BoolT
  | ByteT
  | IntT
  | FloatT
  | TextT
  | RefT of typ
  | TupT of typ list
  | FunT of typ * typ


(* Patterns *)

type lit =
  | IntL of int32
  | FloatL of float
  | TextL of string

type pat = (pat', T.typ) Source.phrase
and pat' =
  | WildP
  | VarP of var
  | LitP of lit
  | ConP of path * pat list
  | RefP of pat
  | TupP of pat list
  | AnnotP of pat * typ


(* Expressions *)

type unop = PosOp | NegOp | InvOp | NotOp
type binop =
  | AddOp | SubOp | MulOp | DivOp | ModOp
  | AndOp | OrOp | XorOp | ShlOp | ShrOp | CatOp
type relop = EqOp | NeOp | LtOp | GtOp | LeOp | GeOp
type logop = AndThenOp | OrElseOp

type exp = (exp', T.typ) Source.phrase
and exp' =
  | VarE of path
  | LitE of lit
  | ConE of path
  | UnE of unop * exp
  | BinE of exp * binop * exp
  | RelE of exp * relop * exp
  | LogE of exp * logop * exp
  | RefE of exp
  | DerefE of exp
  | AssignE of exp * exp
  | TupE of exp list
  | FunE of pat * exp
  | AppE of exp * exp
  | AnnotE of exp * typ
  | IfE of exp * exp * exp
  | CaseE of exp * (pat * exp) list
  | LetE of dec list * exp


(* Declarations *)

and dec = (dec', T.typ * T.str) Source.phrase
and dec' =
  | ExpD of exp
  | AssertD of exp
  | ValD of pat * exp
  | TypD of var * var list * typ
  | DatD of var * var list * (var * typ list) list
  | ModD of var * mod_
  | SigD of var * sig_
  | RecD of dec list
  | InclD of mod_


(* Signatures *)

and spec = (spec', T.str) Source.phrase
and spec' =
  | ValS of var * var list * typ
  | TypS of var * var list * typ option
  | DatS of var * var list * (var * typ list) list
  | ModS of var * sig_
  | SigS of var * sig_
  | RecS of spec list
  | InclS of sig_

and sig_ = (sig', T.sig_) Source.phrase
and sig' =
  | ConS of path
  | StrS of spec list
  | FunS of var * sig_ * sig_
  | WithS of sig_ * path * var list * typ


(* Modules *)

and mod_ = (mod', T.sig_) Source.phrase
and mod' =
  | VarM of path
  | StrM of dec list
  | FunM of var * sig_ * mod_
  | AppM of mod_ * mod_
  | AnnotM of mod_ * sig_
  | LetM of dec list * mod_


(* Programs *)

type imp = (imp', T.str) Source.phrase
and imp' =
  | ImpD of var * string

type prog = (prog', T.typ * T.str) Source.phrase
and prog' =
  | Prog of imp list * dec list
