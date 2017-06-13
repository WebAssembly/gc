(* Types *)

type type_var = Int32.t

type type_ref = ..
type num_type = [`I32Type | `I64Type | `F32Type | `F64Type]
type ref_type = [`RefType of type_ref]
type value_type = [num_type | ref_type]

type stack_type = value_type list
type func_type = [`FuncType of stack_type * stack_type]
type struct_type = [`StructType of value_type list]
type def_type = [func_type | struct_type]

type type_ref += VarType of type_var
type type_ref += RollType of def_type list * Int32.t

type 'a limits = {min : 'a; max : 'a option}
type mutability = Immutable | Mutable
type elem_type = [`AnyFuncType]
type table_type = [`TableType of Int32.t limits * elem_type]
type memory_type = [`MemoryType of Int32.t limits]
type global_type = [`GlobalType of value_type * mutability]
type external_type = [func_type | table_type | memory_type | global_type]


(* Attributes *)

let unknown_type_var = -1l

let is_opaq = function
  | #num_type -> false
  | #ref_type -> true

let size = function
  | `I32Type | `F32Type -> 4
  | `I64Type | `F64Type -> 8


(* Equality *)

let eq_num_type ass t1 t2 = t1 = t2

let rec eq_type_ref ass d1 d2 =
  match d1, d2 with
  | VarType a1, VarType a2 -> a1 = a2
  | RollType (ds1, i1), RollType (ds2, i2) ->
    eq_def_type ass (Lib.List32.nth ds1 i1) (Lib.List32.nth ds2 i2)
  | _, _ -> d1 == d2

and eq_ref_type ass t1 t2 =
  match t1, t2 with
  | `RefType d1, `RefType d2 -> eq_type_ref ass d1 d2

and eq_value_type ass t1 t2 =
  match t1, t2 with
  | (#num_type as t1), (#num_type as t2) -> eq_num_type ass t1 t2
  | (#ref_type as t1), (#ref_type as t2) -> eq_ref_type ass t1 t2
  | _, _ -> false

and eq_value_types ass ts1 ts2 =
  List.length ts1 = List.length ts2 && List.for_all2 (eq_value_type ass) ts1 ts2

and eq_stack_type ass = eq_value_types ass

and eq_func_type ass (`FuncType (ins1, out1)) (`FuncType (ins2, out2)) =
  eq_stack_type ass ins1 ins2 && eq_stack_type ass out1 out2

and eq_struct_type ass (`StructType ts1 as t1) (`StructType ts2 as t2) =
  try List.assq t1 ass == t2
  with Not_found -> eq_value_types ((t1,t2)::ass) ts1 ts2

and eq_def_type ass t1 t2 =
  match t1, t2 with
  | (#func_type as t1), (#func_type as t2) -> eq_func_type ass t1 t2
  | (#struct_type as t1), (#struct_type as t2) -> eq_struct_type ass t1 t2
  | _, _ -> false


(* Closing *)

let close_num_type ds t = t

let rec close_type_ref ds = function
  | VarType a -> RollType (ds, a)
  | t -> t

and close_ref_type ds = function
  | `RefType d -> `RefType (close_type_ref ds d)

and close_value_type ds = function
  | #num_type as t -> close_num_type ds t
  | #ref_type as t -> close_ref_type ds t

and close_value_types ds ts =
  List.map (close_value_type ds) ts

and close_stack_type ds = close_value_types ds

and close_func_type ds = function
  | `FuncType (ins, out) ->
    `FuncType (close_stack_type ds ins, close_stack_type ds out)

and close_struct_type ds = function
  | `StructType ts -> `StructType (close_value_types ds ts)

and close_def_type ds = function
  | #func_type as t -> (close_func_type ds t :> def_type)
  | #struct_type as t -> (close_struct_type ds t :> def_type)


(* Filters *)

let rec funcs = function
  | [] -> []
  | `FuncType ft :: ets -> `FuncType ft :: funcs ets
  | _ :: ets -> funcs ets

let rec tables = function
  | [] -> []
  | `TableType tt :: ets -> `TableType tt :: tables ets
  | _ :: ets -> tables ets

let rec memories = function
  | [] -> []
  | `MemoryType mt :: ets -> `MemoryType mt :: memories ets
  | _ :: ets -> memories ets

let rec globals = function
  | [] -> []
  | `GlobalType ft :: ets -> `GlobalType ft :: globals ets
  | _ :: ets -> globals ets


(* String conversion *)

let string_of_num_type = function
  | `I32Type -> "i32"
  | `I64Type -> "i64"
  | `F32Type -> "f32"
  | `F64Type -> "f64"

let string_of_type_ref = function
  | VarType a -> Int32.to_string a
  | RollType (ts, i) -> "[...]." ^ Int32.to_string i
  | _ -> "?"

let string_of_ref_type = function
  | `RefType d -> "ref(" ^ string_of_type_ref d ^ ")"

let string_of_value_type = function
  | #num_type as t -> string_of_num_type t
  | #ref_type as t -> string_of_ref_type t

let string_of_value_types = function
  | [t] -> string_of_value_type t
  | ts -> "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"


let string_of_stack_type = string_of_value_types

let string_of_func_type = function
  | `FuncType (ins, out) ->
    string_of_stack_type ins ^ " -> " ^ string_of_stack_type out

let string_of_struct_type = function
  | `StructType ts ->
    "(" ^ String.concat " " (List.map string_of_value_type ts) ^ ")"

let string_of_def_type = function
  | #func_type as t -> string_of_func_type t
  | #struct_type as t -> string_of_struct_type t


let string_of_elem_type = function
  | `AnyFuncType -> "anyfunc"

let string_of_limits {min; max} =
  I32.to_string_u min ^
  (match max with None -> "" | Some n -> " " ^ I32.to_string_u n)

let string_of_memory_type = function
  | `MemoryType lim -> string_of_limits lim

let string_of_table_type = function
  | `TableType (lim, t) -> string_of_limits lim ^ " " ^ string_of_elem_type t

let string_of_global_type = function
  | `GlobalType (t, Immutable) -> string_of_value_type t
  | `GlobalType (t, Mutable) -> "(mut " ^ string_of_value_type t ^ ")"

let string_of_extern_type = function
  | #func_type as t -> string_of_func_type t
  | #table_type as t -> string_of_table_type t
  | #memory_type as t -> string_of_memory_type t
  | #global_type as t -> string_of_global_type t
