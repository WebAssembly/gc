(* Types *)

type type_var = Int32.t

type num_type = I32Type | I64Type | F32Type | F64Type
and ref_type = DataRefType of type_desc
and value_type = NumType of num_type | RefType of ref_type

and stack_type = value_type list
and func_type = FuncType of stack_type * stack_type
and struct_type = StructType of value_type list
and def_type = FuncDefType of func_type | StructDefType of struct_type

and type_desc = VarType of type_var | RollType of def_type list * Int32.t

type 'a limits = {min : 'a; max : 'a option}
type mutability = Immutable | Mutable
type elem_type = AnyFuncType
type table_type = TableType of Int32.t limits * elem_type
type memory_type = MemoryType of Int32.t limits
type global_type = GlobalType of value_type * mutability
type external_type =
  | ExternalFuncType of func_type
  | ExternalTableType of table_type
  | ExternalMemoryType of memory_type
  | ExternalGlobalType of global_type


(* Attributes *)

let unknown_type_var = -1l

let is_opaq = function
  | NumType _ -> false
  | RefType _ -> true

let size = function
  | I32Type | F32Type -> 4
  | I64Type | F64Type -> 8


(* Closing *)

let close_num_type ds t = t

let rec close_type_desc ds = function
  | VarType a -> RollType (ds, a)
  | RollType _ as t -> t

and close_ref_type ds = function
  | DataRefType d -> DataRefType (close_type_desc ds d)

and close_value_type ds = function
  | NumType t -> NumType (close_num_type ds t)
  | RefType t -> RefType (close_ref_type ds t)

and close_value_types ds ts =
  List.map (close_value_type ds) ts

and close_stack_type ds = close_value_types ds

and close_func_type ds = function
  | FuncType (ins, out) ->
    FuncType (close_stack_type ds ins, close_stack_type ds out)

and close_struct_type ds = function
  | StructType ts -> StructType (close_value_types ds ts)

and close_def_type ds = function
  | FuncDefType t -> FuncDefType (close_func_type ds t)
  | StructDefType t -> StructDefType (close_struct_type ds t)


(* Equality *)

let svt = ref (fun _ -> failwith "bla")
let sdt = ref (fun _ -> failwith "bla")

let eq_num_type ass t1 t2 = t1 = t2

let rec eq_type_desc ass d1 d2 =
  match d1, d2 with
  | VarType a1, VarType a2 -> a1 = a2
  | RollType (ds1, i1), RollType (ds2, i2) ->
    eq_def_type ass
      (close_def_type ds1 (Lib.List32.nth ds1 i1))
      (close_def_type ds2 (Lib.List32.nth ds2 i2))
  | _, _ -> d1 == d2

and eq_ref_type ass t1 t2 =
  match t1, t2 with
  | DataRefType d1, DataRefType d2 -> eq_type_desc ass d1 d2

and eq_value_type ass t1 t2 =
Printf.printf "[eq_value_type %s %s] %s\n" (!svt t1) (!svt t2) (String.concat " " (List.map (fun (t1,t2) -> !sdt t1 ^"="^ !sdt t2) ass));flush_all ();
  match t1, t2 with
  | NumType t1, NumType t2 -> eq_num_type ass t1 t2
  | RefType t1, RefType t2 -> eq_ref_type ass t1 t2
  | _, _ -> false

and eq_value_types ass ts1 ts2 =
  List.length ts1 = List.length ts2 && List.for_all2 (eq_value_type ass) ts1 ts2

and eq_stack_type ass = eq_value_types ass

and eq_func_type ass t1 t2 =
  match t1, t2 with
  | FuncType (ins1, out1), FuncType (ins2, out2) ->
    eq_stack_type ass ins1 ins2 && eq_stack_type ass out1 out2

and eq_struct_type ass t1 t2 =
Printf.printf "[eq_struct_type %s %s] %s\n" (!sdt t1) (!sdt t2) (String.concat " " (List.map (fun (t1,t2) -> !sdt t1 ^"="^ !sdt t2) ass));flush_all ();
  match t1, t2 with
  | StructType ts1, StructType ts2 ->
    List.exists ((=) (t1,t2)) ass || eq_value_types ((t1,t2)::ass) ts1 ts2

and eq_def_type ass t1 t2 =
  match t1, t2 with
  | FuncDefType t1, FuncDefType t2 -> eq_func_type ass t1 t2
  | StructDefType t1, StructDefType t2 -> eq_struct_type ass t1 t2
  | _, _ -> false


(* Filters *)

let rec funcs = function
  | [] -> []
  | ExternalFuncType ft :: ets -> ft :: funcs ets
  | _ :: ets -> funcs ets

let rec tables = function
  | [] -> []
  | ExternalTableType tt :: ets -> tt :: tables ets
  | _ :: ets -> tables ets

let rec memories = function
  | [] -> []
  | ExternalMemoryType mt :: ets -> mt :: memories ets
  | _ :: ets -> memories ets

let rec globals = function
  | [] -> []
  | ExternalGlobalType ft :: ets -> ft :: globals ets
  | _ :: ets -> globals ets


(* String conversion *)

let string_of_num_type = function
  | I32Type -> "i32"
  | I64Type -> "i64"
  | F32Type -> "f32"
  | F64Type -> "f64"

let string_of_type_desc = function
  | VarType a -> Int32.to_string a
  | RollType (ts, i) -> "[...] " ^ Int32.to_string i

let string_of_ref_type = function
  | DataRefType d -> "(ref " ^ string_of_type_desc d ^ ")"

let string_of_value_type = function
  | NumType t -> string_of_num_type t
  | RefType t -> string_of_ref_type t

let string_of_value_types = function
  | [t] -> string_of_value_type t
  | ts -> "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"


let string_of_stack_type = string_of_value_types

let string_of_func_type = function
  | FuncType (ins, out) ->
    string_of_stack_type ins ^ " -> " ^ string_of_stack_type out

let string_of_struct_type = function
  | StructType ts ->
    "(" ^ String.concat " " (List.map string_of_value_type ts) ^ ")"

let string_of_def_type = function
  | FuncDefType t -> string_of_func_type t
  | StructDefType t -> string_of_struct_type t
let _ = svt := string_of_value_type
let _ = sdt := string_of_struct_type

let string_of_elem_type = function
  | AnyFuncType -> "anyfunc"

let string_of_limits {min; max} =
  I32.to_string_u min ^
  (match max with None -> "" | Some n -> " " ^ I32.to_string_u n)

let string_of_memory_type = function
  | MemoryType lim -> string_of_limits lim

let string_of_table_type = function
  | TableType (lim, t) -> string_of_limits lim ^ " " ^ string_of_elem_type t

let string_of_global_type = function
  | GlobalType (t, Immutable) -> string_of_value_type t
  | GlobalType (t, Mutable) -> "(mut " ^ string_of_value_type t ^ ")"

let string_of_external_type = function
  | ExternalFuncType t -> string_of_func_type t
  | ExternalTableType t -> string_of_table_type t
  | ExternalMemoryType t -> string_of_memory_type t
  | ExternalGlobalType t -> string_of_global_type t
