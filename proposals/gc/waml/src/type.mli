(* Types *)

type var = string
type pred = Any | Eq | Ord | Num
type arity = UnknownArity | KnownArity of int | VariableArity

type typ =
  | Var of var * typ list
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Ref of typ
  | Tup of typ list
  | Fun of typ * typ * arity ref
  | Data of typ
  | Pack of sig_
  | Infer of infer ref

and infer =
  | Unres of string * pred
  | Res of typ

and poly = Forall of var list * typ
and con = Lambda of var list * typ

and sig_ =
  | Str of var list * str
  | Fct of var list * sig_ * sig_

and str = (poly, con, sig_, sig_) Env.env


(* Constructors and Accessors *)

val var : var -> typ
val fun_flat : typ list -> typ -> typ

val is_fun : typ -> bool

val as_tup : typ -> typ list
val as_fun : typ -> typ * typ * arity ref
val as_fun_flat : typ -> typ list * typ
val as_data : typ -> typ

val as_poly : poly -> var list * typ
val as_mono : poly -> typ

val as_str : sig_ -> var list * str
val as_fct : sig_ -> var list * sig_ * sig_


(* Substitutions *)

type subst

val subst : subst -> typ -> typ
val subst_sig : subst -> sig_ -> sig_
val subst_str : subst -> str -> str

val is_empty_subst : subst -> bool
val empty_subst : subst
val adjoin_subst : subst -> subst -> subst

val lookup_subst : subst -> var -> con option
val extend_subst : subst -> var -> con -> subst
val extend_subst_typ : subst -> var -> typ -> subst

val con_subst : var list -> con list -> subst
val typ_subst : var list -> typ list -> subst
val var_subst : var list -> var list -> subst


(* Operations *)

exception Unify of typ * typ
exception Mismatch of string

val eq : typ -> typ -> bool
val eq_con : con -> con -> bool
val unify : typ -> typ -> unit (* raises Unify *)
val infer : pred -> typ
val norm : typ -> typ

val inst : poly -> typ
val generalize : str -> poly -> poly

val default_sig : sig_ -> unit
val default_str : str -> unit

val fresh_for : Env.Set.t -> string -> var

val free : typ -> Env.Set.t
val free_poly : poly -> Env.Set.t
val free_sig : sig_ -> Env.Set.t
val free_str : str -> Env.Set.t

val string_of_typ : typ -> string
val string_of_poly : poly -> string
val string_of_sig : sig_ -> string
val string_of_str : str -> string

val pack : var list -> sig_ -> sig_
val unpack : var -> sig_ -> var list * sig_

val sub : sig_ -> sig_ -> subst (* raises Mismatch *)
