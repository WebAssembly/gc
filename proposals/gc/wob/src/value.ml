module Env = Map.Make(String)

type var = string
type typ = Type.typ

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
    typs : Type.env;
  }


(* Environmets *)

let empty_env = {vals = Env.empty; typs = Type.empty_env}

let extend_val env x v = {env with vals = Env.add x (ref v) env.vals}
let extend_typ env x c = {env with typs = Type.extend env.typs x c}
let extend_typ_gnd env x t = {env with typs = Type.extend_gnd env.typs x t}
let extend_typ_abs env x = {env with typs = Type.extend_abs env.typs x}

let val_env x v = extend_val empty_env x v
let typ_env x c = extend_typ empty_env x c

let adjoin_env env1 env2 =
  { vals = Env.union (fun _ x1 x2 -> Some x2) env1.vals env2.vals;
    typs = Type.adjoin_env env1.typs env2.typs;
  }

let lookup_val env x = Env.find_opt x env.vals
let lookup_typ env x = Type.lookup env.typs x


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
