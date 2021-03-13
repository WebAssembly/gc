(* Types *)

type value =
  | Byte of char
  | Int of int32
  | Float of float
  | Text of string
  | Tup of value list
  | Con of string * value list
  | Ref of value ref
  | Fun of ((string * value) list -> value -> value)

type module_ =
  | Str of (string * value) list * (string * module_) list
  | Fct of (module_ -> module_)


(* Conversion *)

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

let close xvs = function
  | Fun f -> Fun (fun _ -> f xvs)
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

let seq f xs = String.concat " " (List.map f xs)
let list f xs = String.concat ", " (List.map f xs)

let rec to_string = function
  | Byte c -> Printf.sprintf "0x%02x" (Char.code c)
  | Int i -> Int32.to_string i
  | Float z -> string_of_float z
  | Text t -> "\"" ^ String.escaped t ^ "\""
  | Tup vs -> "(" ^ list to_string vs ^ ")"
  | Con (x, []) -> x
  | Con (x, vs) -> "(" ^ x ^ " " ^ seq to_string vs ^ ")"
  | Ref r -> "(ref " ^ to_string !r ^ ")"
  | Fun _ -> "fun"
