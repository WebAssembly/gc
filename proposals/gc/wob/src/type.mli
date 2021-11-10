(* Types *)

type var = string
type kind = int
type mut = Mut | Const
type sort = LetS | VarS | FuncS | ClassS | ProhibitedS

type typ =
  | Var of var * typ list
  | Bot
  | Null
  | Bool
  | Byte
  | Int
  | Float
  | Text
  | Obj
  | Boxed
  | Box of typ
  | Tup of typ list
  | Array of typ * mut
  | Func of var list * typ list * typ
  | Inst of cls * typ list
  | Class of cls

and cls =
  { name : var;
    id : int;
    tparams : var list;
    mutable vparams : typ list;
    mutable sup : typ;
    mutable def : (var * (sort * typ)) list;
  }


(* Constructors and accessors *)

val var : var -> typ

val is_var : typ -> bool
val is_inst : typ -> bool

val as_tup : typ -> typ list
val as_array : typ -> typ * mut
val as_func : typ -> var list * typ list * typ
val as_inst : typ -> cls * typ list
val as_class : typ -> cls


(* Operations *)

val eq : typ -> typ -> bool
val sub : typ -> typ -> bool
val lub : typ -> typ -> typ (* raises Failure *)

val free : typ -> Env.Set.t

val to_string : typ -> string


(* Classes *)

val gen_cls : 'id -> var -> var list -> cls
val eq_cls : cls -> cls -> bool

val sup_cls : cls -> cls option
val cls_depth : cls -> int


(* Substitutions *)

module Subst = Env.Map

type con = typ list -> typ
type subst = con Subst.t

val subst : subst -> typ -> typ

val empty_subst : subst
val adjoin_subst : subst -> subst -> subst

val lookup_subst : subst -> var -> con option
val extend_subst : subst -> var -> con -> subst
val extend_subst_typ : subst -> var -> typ -> subst
val extend_subst_abs : subst -> var -> subst

val typ_subst : var list -> typ list -> subst
