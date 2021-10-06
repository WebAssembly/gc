(* Types *)

type typ = Type.typ

and func = (Type.sort * value) Env.Map.t -> typ list -> value list -> value

and value =
  | Null
  | Bool of bool
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Box of value
  | Tup of value list
  | Array of value ref list
  | Obj of typ * obj
  | Func of func
  | Class of Type.cls * func * cls

and obj = (Type.sort * value ref) Env.Map.t ref
and cls = (Type.sort * value) Env.Map.t -> typ -> typ list -> value list -> value * (unit -> unit)


(* Accessors *)

let as_obj = function Obj (_, obj) -> obj | _ -> assert false


(* Recursive closure *)

let fix env = function
  | Func f -> Func (fun _ -> f env)
  | Class (c, f, cls) -> Class (c, (fun _ -> f env), cls)
  | _ -> assert false


(* Comparison *)

let is_ref = function
  | Null | Bool _ | Byte _ | Int _ | Float _ | Text _ -> false
  | Box _ | Tup _ -> false
  | Array _ | Obj _ | Func _ | Class _ -> true

let rec eq v1 v2 =
  v1 == v2 ||
  match v1, v2 with
  | Box v1, Box v2 -> eq v1 v2
  | Tup vs1, Tup vs2 ->
    List.length vs1 = List.length vs2 && List.for_all2 eq vs1 vs2
  | v1, v2 when is_ref v1 && is_ref v2 -> v1 == v2
  | v1, v2 when not (is_ref v1) && not (is_ref v2) -> v1 = v2
  | _, _ -> false


(* Default *)

let rec default = function
  | Type.(Var _ | Bot) -> assert false
  | Type.(Null | Boxed | Obj | Array _ | Func _ | Inst _ | Class _) -> Null
  | Type.Bool -> Bool false
  | Type.Byte -> Byte '\x00'
  | Type.Int -> Int 0l
  | Type.Float -> Float 0.0
  | Type.Text -> Text ""
  | Type.Box t -> Box (default t)
  | Type.Tup ts -> Tup (List.map default ts)


(* Printing *)

let list f xs = String.concat ", " (List.map f xs)

let rec to_string = function
  | Null -> "null"
  | Bool b -> string_of_bool b
  | Byte c -> Printf.sprintf "0x%02x" (Char.code c)
  | Int i -> Int32.to_string i
  | Float z -> string_of_float z
  | Text t -> "\"" ^ String.escaped t ^ "\""
  | Box v -> to_string v ^ "$"
  | Tup vs -> "(" ^ list to_string vs ^ ")"
  | Array vs -> "[" ^ list to_string (List.map (!) vs) ^ "]"
  | Obj (t, _) -> "(new " ^ Type.to_string t ^ ")"
  | Func _ -> "func"
  | Class _ -> "class"
