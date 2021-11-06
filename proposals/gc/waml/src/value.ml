open Source

module S = Env


(* Types *)

type var = string

type value =
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Con of var * value list
  | Ref of value ref
  | Fun of ((var * value) list -> value -> value)
  | Pack of module_

and module_ =
  | Str of str
  | Fct of (module_ -> module_)

and str = (value, unit, module_, unit) S.env


(* Conversion *)

let int i = Int Int32.(shift_right (shift_left i 1) 1)

let is_bool = function
  | Con (("True" | "False"), []) -> true
  | _ -> false

let of_bool = function
  | true -> Con ("True", [])
  | false -> Con ("False", [])

let to_bool = function
  | Con ("True", []) -> true
  | Con ("False", []) -> false
  | _ -> assert false

let con x n =
  let rec f vs = function
    | 0 -> Con (x, List.rev vs)
    | n -> Fun (fun _ v -> f (v::vs) (n - 1))
  in f [] n


(* Recursive closure *)

let fix xvs = function
  | Fun f -> Fun (fun _ -> f xvs)
  | Con _ as v -> v
  | _ -> assert false


(* Comparison *)

let rec eq v1 v2 =
  match v1, v2 with
  | Tup vs1, Tup vs2 ->
    List.length vs1 = List.length vs2 && List.for_all2 eq vs1 vs2
  | Con (x1, vs1), Con (x2, vs2) ->
    x1 = x2 && List.length vs1 = List.length vs2 && List.for_all2 eq vs1 vs2
  | Ref r1, Ref r2 -> r1 == r2
  | v1, v2 -> v1 = v2


(* Printing *)

let list sep f xs = String.concat sep (List.map f xs)

let rec string_of_value = function
  | Con (x, vs) when vs <> [] -> x ^ " " ^ list " " string_of_value_simple vs
  | Ref r -> "ref " ^ string_of_value_simple !r
  | v -> string_of_value_simple v

and string_of_value_simple = function
  | Byte c -> Printf.sprintf "0x%02x" (Char.code c)
  | Int i -> Int32.to_string i
  | Float z -> string_of_float z
  | Text t -> "\"" ^ String.escaped t ^ "\""
  | Tup vs -> "(" ^ list ", " string_of_value vs ^ ")"
  | Con (x, []) -> x
  | Fun _ -> "(fun)"
  | Pack m -> "(pack " ^ string_of_module m ^ ")"
  | v -> "(" ^ string_of_value v ^ ")"

and string_of_module = function
  | Str s ->
    let vs = List.map string_of_val (S.vals s) in
    let ms = List.map string_of_mod (S.mods s) in
    let xs = List.sort compare_by_region (ms @ vs) in
    "{" ^ String.concat "; " (List.map it xs) ^ "}"
  | Fct _ -> "fct"

and string_of_val (x, v) = ("val " ^ x ^ " = " ^ string_of_value v.it) @@ v.at
and string_of_mod (x, m) = ("module " ^ x ^ " = " ^ string_of_module m.it) @@ m.at
