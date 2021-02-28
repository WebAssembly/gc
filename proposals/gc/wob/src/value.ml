module Env = Map.Make(String)

type var = Syntax.var
type typ = Syntax.typ

and con = typ list -> typ
and func = typ list -> value list -> value

and value =
  | Null
  | Bool of bool
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Array of value ref list
  | Obj of typ * env
  | Func of func
  | Class of func

and env =
  { vals : value ref Env.t;
    typs : con Env.t;
  }


(* Environmets *)

let empty_env = {vals = Env.empty; typs = Env.empty}

let extend_val env x v = {env with vals = Env.add x.Source.it (ref v) env.vals}
let extend_typ env x c = {env with typs = Env.add x.Source.it c env.typs}
let extend_typ_gnd env x t = extend_typ env x (fun _ -> t)
let extend_typ_abs env x =
  let open Source in extend_typ_gnd env x (Syntax.VarT (x, []) @@ x.at)

let val_env x v = extend_val empty_env x v
let typ_env x c = extend_typ empty_env x c

let adjoin_env env1 env2 =
  { vals = Env.union (fun _ x1 x2 -> Some x2) env1.vals env2.vals;
    typs = Env.union (fun _ x1 x2 -> Some x2) env1.typs env2.typs;
  }

let lookup_val env x = Env.find_opt x.Source.it env.vals
let lookup_typ env x = Env.find_opt x.Source.it env.typs


(* Printing *)

let rec string_of_value = function
  | Null -> "null"
  | Bool b -> string_of_bool b
  | Byte c -> Printf.sprintf "0x%02x" (Char.code c)
  | Int i -> Int32.to_string i
  | Float z -> string_of_float z
  | Text t -> "\"" ^ String.escaped t ^ "\""
  | Tup vs -> "(" ^ String.concat ", " (List.map string_of_value vs) ^ ")"
  | Array vs ->
    "[" ^ String.concat ", " (List.map string_of_value (List.map (!) vs)) ^ "]"
  | Obj (t, _) -> "new"  (* TODO *)
  | Func _ -> "func"
  | Class _ -> "class"
