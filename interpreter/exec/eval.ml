open Types
open Value
open Instance
open Ast
open Source


(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

let table_error at = function
  | Table.Bounds -> "out of bounds table access"
  | Table.SizeOverflow -> "table size overflow"
  | Table.SizeLimit -> "table size limit reached"
  | Table.Type -> Crash.error at "type mismatch at table access"
  | exn -> raise exn

let memory_error at = function
  | Memory.Bounds -> "out of bounds memory access"
  | Memory.SizeOverflow -> "memory size overflow"
  | Memory.SizeLimit -> "memory size limit reached"
  | Memory.Type -> Crash.error at "type mismatch at memory access"
  | exn -> raise exn

let numeric_error at = function
  | Ixx.Overflow -> "integer overflow"
  | Ixx.DivideByZero -> "integer divide by zero"
  | Ixx.InvalidConversion -> "invalid conversion to integer"
  | Value.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ string_of_num_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ string_of_num_type (type_of_num v))
  | exn -> raise exn


(* Administrative Expressions & Configurations *)

type 'a stack = 'a list

type frame =
{
  inst : module_inst;
  locals : value ref list;
}

type code = value stack * admin_instr list

and admin_instr = admin_instr' phrase
and admin_instr' =
  | Plain of instr'
  | Refer of ref_
  | Invoke of func_inst
  | Trapping of string
  | Returning of value stack
  | ReturningInvoke of value stack * func_inst
  | Breaking of int32 * value stack
  | Label of int * instr list * code
  | Local of int * value list * code
  | Frame of int * frame * code

type config =
{
  frame : frame;
  code : code;
  budget : int;  (* to model stack overflow *)
}

let frame inst = {inst; locals = []}
let config inst vs es = {frame = frame inst; code = vs, es; budget = 300}

let plain e = Plain e.it @@ e.at

let is_jumping e =
  match e.it with
  | Trapping _ | Returning _ | ReturningInvoke _ | Breaking _ -> true
  | _ -> false

let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let memory (inst : module_inst) x = lookup "memory" inst.memories x
let global (inst : module_inst) x = lookup "global" inst.globals x
let elem (inst : module_inst) x = lookup "element segment" inst.elems x
let data (inst : module_inst) x = lookup "data segment" inst.datas x
let local (frame : frame) x = lookup "local" frame.locals x

let str_type (inst : module_inst) x = expand_ctx_type (def_of (type_ inst x))
let func_type (inst : module_inst) x = as_func_str_type (str_type inst x)
let struct_type (inst : module_inst) x = as_struct_str_type  (str_type inst x)
let array_type (inst : module_inst) x = as_array_str_type (str_type inst x)

let any_ref inst x i at =
  try Table.load (table inst x) i with Table.Bounds ->
    Trap.error at ("undefined element " ^ Int32.to_string i)

let func_ref inst x i at =
  match any_ref inst x i at with
  | FuncRef f -> f
  | NullRef _ -> Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i)

let block_type inst bt at =
  match bt with
  | ValBlockType None -> FuncType ([], [])
  | ValBlockType (Some t) -> FuncType ([], [t])
  | VarBlockType (SynVar x) -> func_type inst (x @@ at)
  | VarBlockType (SemVar x) -> as_func_str_type (expand_ctx_type (def_of x))
  | VarBlockType (RecVar _) -> assert false

let take n (vs : 'a stack) at =
  try Lib.List.take n vs with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Lib.List.drop n vs with Failure _ -> Crash.error at "stack underflow"

let split n (vs : 'a stack) at = take n vs at, drop n vs at


(* Evaluation *)

(*
 * Conventions:
 *   e  : instr
 *   v  : value
 *   es : instr list
 *   vs : value stack
 *   c : config
 *)

let mem_oob frame x i n =
  I64.gt_u (I64.add (I64_convert.extend_i32_u i) (I64_convert.extend_i32_u n))
    (Memory.bound (memory frame.inst x))

let data_oob frame x i n =
  I64.gt_u (I64.add (I64_convert.extend_i32_u i) (I64_convert.extend_i32_u n))
    (I64.of_int_u (String.length !(data frame.inst x)))

let table_oob frame x i n =
  I64.gt_u (I64.add (I64_convert.extend_i32_u i) (I64_convert.extend_i32_u n))
    (I64_convert.extend_i32_u (Table.size (table frame.inst x)))

let elem_oob frame x i n =
  I64.gt_u (I64.add (I64_convert.extend_i32_u i) (I64_convert.extend_i32_u n))
    (I64.of_int_u (List.length !(elem frame.inst x)))

let rec step (c : config) : config =
  let vs, es = c.code in
  let e = List.hd es in
  let vs', es' =
    match e.it, vs with
    | Plain e', vs ->
      (match e', vs with
      | Unreachable, vs ->
        vs, [Trapping "unreachable executed" @@ e.at]

      | Nop, vs ->
        vs, []

      | Block (bt, es'), vs ->
        let FuncType (ts1, ts2) = block_type c.frame.inst bt e.at in
        let n1 = List.length ts1 in
        let n2 = List.length ts2 in
        let args, vs' = split n1 vs e.at in
        vs', [Label (n2, [], (args, List.map plain es')) @@ e.at]

      | Loop (bt, es'), vs ->
        let FuncType (ts1, ts2) = block_type c.frame.inst bt e.at in
        let n1 = List.length ts1 in
        let args, vs' = split n1 vs e.at in
        vs', [Label (n1, [e' @@ e.at], (args, List.map plain es')) @@ e.at]

      | If (bt, es1, es2), Num (I32 i) :: vs' ->
        if i = 0l then
          vs', [Plain (Block (bt, es2)) @@ e.at]
        else
          vs', [Plain (Block (bt, es1)) @@ e.at]

      | Let (bt, locals, es'), vs ->
        let vs0, vs' = split (List.length locals) vs e.at in
        let FuncType (ts1, ts2) = block_type c.frame.inst bt e.at in
        let vs1, vs2 = split (List.length ts1) vs' e.at in
        vs2, [
          Local (List.length ts2, List.rev vs0,
            (vs1, [Plain (Block (bt, es')) @@ e.at])
          ) @@ e.at
        ]

      | Br x, vs ->
        [], [Breaking (x.it, vs) @@ e.at]

      | BrIf x, Num (I32 i) :: vs' ->
        if i = 0l then
          vs', []
        else
          vs', [Plain (Br x) @@ e.at]

      | BrTable (xs, x), Num (I32 i) :: vs' ->
        if I32.ge_u i (Lib.List32.length xs) then
          vs', [Plain (Br x) @@ e.at]
        else
          vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at]

      | BrCast (x, NullOp), Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          vs', [Plain (Br x) @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | BrCast (x, I31Op), Ref r :: vs' ->
        (match r with
        | I31.I31Ref _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | BrCast (x, DataOp), Ref r :: vs' ->
        (match r with
        | Data.DataRef _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | BrCast (x, ArrayOp), Ref r :: vs' ->
        (match r with
        | Data.DataRef (Data.Array _) ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | BrCast (x, FuncOp), Ref r :: vs' ->
        (match r with
        | FuncRef _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | BrCast (x, RttOp), Ref (NullRef _) :: vs' ->
        vs', [Trapping "null RTT reference" @@ e.at]

      | BrCast (x, RttOp), Ref (Rtt.RttRef rtt) :: Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | Data.DataRef d when Rtt.match_rtt (Data.read_rtt d) rtt ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | FuncRef f when Rtt.match_rtt (Func.read_rtt f) rtt ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | Data.DataRef _ | FuncRef _ ->
          Ref r :: vs', []
        | _ ->
          Crash.error e.at "wrong reference type"
        )

      | BrCastFail (x, NullOp), Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          vs', []
        | _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        )

      | BrCastFail (x, I31Op), Ref r :: vs' ->
        (match r with
        | I31.I31Ref _ ->
          Ref r :: vs', []
        | _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        )

      | BrCastFail (x, DataOp), Ref r :: vs' ->
        (match r with
        | Data.DataRef _ ->
          Ref r :: vs', []
        | _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        )

      | BrCastFail (x, ArrayOp), Ref r :: vs' ->
        (match r with
        | Data.DataRef (Data.Array _) ->
          Ref r :: vs', []
        | _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        )

      | BrCastFail (x, FuncOp), Ref r :: vs' ->
        (match r with
        | FuncRef _ ->
          Ref r :: vs', []
        | _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        )

      | BrCastFail (x, RttOp), Ref (NullRef _) :: vs' ->
        vs', [Trapping "null RTT reference" @@ e.at]

      | BrCastFail (x, RttOp), Ref (Rtt.RttRef rtt) :: Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          Ref r :: vs', []
        | Data.DataRef d when Rtt.match_rtt (Data.read_rtt d) rtt ->
          Ref r :: vs', []
        | FuncRef f when Rtt.match_rtt (Func.read_rtt f) rtt ->
          Ref r :: vs', []
        | Data.DataRef _ | FuncRef _ ->
          Ref r :: vs', [Plain (Br x) @@ e.at]
        | _ ->
          Crash.error e.at "wrong reference type"
        )

      | Return, vs ->
        [], [Returning vs @@ e.at]

      | Call x, vs ->
        vs, [Invoke (func c.frame.inst x) @@ e.at]

      | CallRef, Ref (NullRef _) :: vs ->
        vs, [Trapping "null function reference" @@ e.at]

      | CallRef, Ref (FuncRef f) :: vs ->
        vs, [Invoke f @@ e.at]

      | CallIndirect (x, y), Num (I32 i) :: vs ->
        let f = func_ref c.frame.inst x i e.at in
        if
          Match.match_var_type []
            (SemVar (Func.type_inst_of f))
            (sem_var_type c.frame.inst.types (SynVar y.it))
        then
          vs, [Invoke f @@ e.at]
        else
          vs, [Trapping "indirect call type mismatch" @@ e.at]

      | ReturnCallRef, Ref (NullRef _) :: vs ->
        vs, [Trapping "null function reference" @@ e.at]

      | ReturnCallRef, vs ->
        (match (step {c with code = (vs, [Plain CallRef @@ e.at])}).code with
        | vs', [{it = Invoke a; at}] -> vs', [ReturningInvoke (vs', a) @@ at]
        | vs', [{it = Trapping s; at}] -> vs', [Trapping s @@ at]
        | _ -> assert false
        )

      | FuncBind x, Ref (NullRef _) :: vs ->
        vs, [Trapping "null function reference" @@ e.at]

      | FuncBind x, Ref (FuncRef f) :: vs ->
        let FuncType (ts, _) = Func.type_of f in
        let FuncType (ts', _) = func_type c.frame.inst x in
        let args, vs' =
          try split (List.length ts - List.length ts') vs e.at
          with Failure _ -> Crash.error e.at "type mismatch at function bind"
        in
        let f' = Func.alloc_closure (type_ c.frame.inst x) f args in
        Ref (FuncRef f') :: vs', []

      | Drop, v :: vs' ->
        vs', []

      | Select _, Num (I32 i) :: v2 :: v1 :: vs' ->
        if i = 0l then
          v2 :: vs', []
        else
          v1 :: vs', []

      | LocalGet x, vs ->
        !(local c.frame x) :: vs, []

      | LocalSet x, v :: vs' ->
        local c.frame x := v;
        vs', []

      | LocalTee x, v :: vs' ->
        local c.frame x := v;
        v :: vs', []

      | GlobalGet x, vs ->
        Global.load (global c.frame.inst x) :: vs, []

      | GlobalSet x, v :: vs' ->
        (try Global.store (global c.frame.inst x) v; vs', []
        with Global.NotMutable -> Crash.error e.at "write to immutable global"
           | Global.Type -> Crash.error e.at "type mismatch at global write")

      | TableGet x, Num (I32 i) :: vs' ->
        (try Ref (Table.load (table c.frame.inst x) i) :: vs', []
        with exn -> vs', [Trapping (table_error e.at exn) @@ e.at])

      | TableSet x, Ref r :: Num (I32 i) :: vs' ->
        (try Table.store (table c.frame.inst x) i r; vs', []
        with exn -> vs', [Trapping (table_error e.at exn) @@ e.at])

      | TableSize x, vs ->
        Num (I32 (Table.size (table c.frame.inst x))) :: vs, []

      | TableGrow x, Num (I32 delta) :: Ref r :: vs' ->
        let tab = table c.frame.inst x in
        let old_size = Table.size tab in
        let result =
          try Table.grow tab delta r; old_size
          with Table.SizeOverflow | Table.SizeLimit | Table.OutOfMemory -> -1l
        in Num (I32 result) :: vs', []

      | TableFill x, Num (I32 n) :: Ref r :: Num (I32 i) :: vs' ->
        if table_oob c.frame x i n then
          vs', [Trapping (table_error e.at Table.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else
          let _ = assert (I32.lt_u i 0xffff_ffffl) in
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 i @@ e.at));
            Refer r;
            Plain (TableSet x);
            Plain (Const (I32 (I32.add i 1l) @@ e.at));
            Refer r;
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (TableFill x);
          ]

      | TableCopy (x, y), Num (I32 n) :: Num (I32 s) :: Num (I32 d) :: vs' ->
        if table_oob c.frame x d n || table_oob c.frame y s n then
          vs', [Trapping (table_error e.at Table.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else if I32.le_u d s then
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 d @@ e.at));
            Plain (Const (I32 s @@ e.at));
            Plain (TableGet y);
            Plain (TableSet x);
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (TableCopy (x, y));
          ]
        else (* d > s *)
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (TableCopy (x, y));
            Plain (Const (I32 d @@ e.at));
            Plain (Const (I32 s @@ e.at));
            Plain (TableGet y);
            Plain (TableSet x);
          ]

      | TableInit (x, y), Num (I32 n) :: Num (I32 s) :: Num (I32 d) :: vs' ->
        if table_oob c.frame x d n || elem_oob c.frame y s n then
          vs', [Trapping (table_error e.at Table.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else
          let seg = !(elem c.frame.inst y) in
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 d @@ e.at));
            Refer (List.nth seg (Int32.to_int s));
            Plain (TableSet x);
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (TableInit (x, y));
          ]

      | ElemDrop x, vs ->
        let seg = elem c.frame.inst x in
        seg := [];
        vs, []

      | Load {offset; ty; pack; _}, Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let a = I64_convert.extend_i32_u i in
        (try
          let n =
            match pack with
            | None -> Memory.load_num mem a offset ty
            | Some (sz, ext) -> Memory.load_num_packed sz ext mem a offset ty
          in Num n :: vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])

      | Store {offset; pack; _}, Num n :: Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let a = I64_convert.extend_i32_u i in
        (try
          (match pack with
          | None -> Memory.store_num mem a offset n
          | Some sz -> Memory.store_num_packed sz mem a offset n
          );
          vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at]);

      | VecLoad {offset; ty; pack; _}, Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let addr = I64_convert.extend_i32_u i in
        (try
          let v =
            match pack with
            | None -> Memory.load_vec mem addr offset ty
            | Some (sz, ext) ->
              Memory.load_vec_packed sz ext mem addr offset ty
          in Vec v :: vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])

      | VecStore {offset; _}, Vec v :: Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let addr = I64_convert.extend_i32_u i in
        (try
          Memory.store_vec mem addr offset v;
          vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at]);

      | VecLoadLane ({offset; ty; pack; _}, j), Vec (V128 v) :: Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let addr = I64_convert.extend_i32_u i in
        (try
          let v =
            match pack with
            | Pack8 ->
              V128.I8x16.replace_lane j v
                (I32Num.of_num 0 (Memory.load_num_packed Pack8 SX mem addr offset I32Type))
            | Pack16 ->
              V128.I16x8.replace_lane j v
                (I32Num.of_num 0 (Memory.load_num_packed Pack16 SX mem addr offset I32Type))
            | Pack32 ->
              V128.I32x4.replace_lane j v
                (I32Num.of_num 0 (Memory.load_num mem addr offset I32Type))
            | Pack64 ->
              V128.I64x2.replace_lane j v
                (I64Num.of_num 0 (Memory.load_num mem addr offset I64Type))
          in Vec (V128 v) :: vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])

      | VecStoreLane ({offset; ty; pack; _}, j), Vec (V128 v) :: Num (I32 i) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let addr = I64_convert.extend_i32_u i in
        (try
          (match pack with
          | Pack8 ->
            Memory.store_num_packed Pack8 mem addr offset (I32 (V128.I8x16.extract_lane_s j v))
          | Pack16 ->
            Memory.store_num_packed Pack16 mem addr offset (I32 (V128.I16x8.extract_lane_s j v))
          | Pack32 ->
            Memory.store_num mem addr offset (I32 (V128.I32x4.extract_lane_s j v))
          | Pack64 ->
            Memory.store_num mem addr offset (I64 (V128.I64x2.extract_lane_s j v))
          );
          vs', []
        with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])

      | MemorySize, vs ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        Num (I32 (Memory.size mem)) :: vs, []

      | MemoryGrow, Num (I32 delta) :: vs' ->
        let mem = memory c.frame.inst (0l @@ e.at) in
        let old_size = Memory.size mem in
        let result =
          try Memory.grow mem delta; old_size
          with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
        in Num (I32 result) :: vs', []

      | MemoryFill, Num (I32 n) :: Num k :: Num (I32 i) :: vs' ->
        if mem_oob c.frame (0l @@ e.at) i n then
          vs', [Trapping (memory_error e.at Memory.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 i @@ e.at));
            Plain (Const (k @@ e.at));
            Plain (Store
              {ty = I32Type; align = 0; offset = 0l; pack = Some Pack8});
            Plain (Const (I32 (I32.add i 1l) @@ e.at));
            Plain (Const (k @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (MemoryFill);
          ]

      | MemoryCopy, Num (I32 n) :: Num (I32 s) :: Num (I32 d) :: vs' ->
        if mem_oob c.frame (0l @@ e.at) s n || mem_oob c.frame (0l @@ e.at) d n then
          vs', [Trapping (memory_error e.at Memory.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else if I32.le_u d s then
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 d @@ e.at));
            Plain (Const (I32 s @@ e.at));
            Plain (Load
              {ty = I32Type; align = 0; offset = 0l; pack = Some (Pack8, ZX)});
            Plain (Store
              {ty = I32Type; align = 0; offset = 0l; pack = Some Pack8});
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (MemoryCopy);
          ]
        else (* d > s *)
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (MemoryCopy);
            Plain (Const (I32 d @@ e.at));
            Plain (Const (I32 s @@ e.at));
            Plain (Load
              {ty = I32Type; align = 0; offset = 0l; pack = Some (Pack8, ZX)});
            Plain (Store
              {ty = I32Type; align = 0; offset = 0l; pack = Some Pack8});
          ]

      | MemoryInit x, Num (I32 n) :: Num (I32 s) :: Num (I32 d) :: vs' ->
        if mem_oob c.frame (0l @@ e.at) d n || data_oob c.frame x s n then
          vs', [Trapping (memory_error e.at Memory.Bounds) @@ e.at]
        else if n = 0l then
          vs', []
        else
          let seg = !(data c.frame.inst x) in
          let b = Int32.of_int (Char.code seg.[Int32.to_int s]) in
          vs', List.map (Lib.Fun.flip (@@) e.at) [
            Plain (Const (I32 d @@ e.at));
            Plain (Const (I32 b @@ e.at));
            Plain (Store
              {ty = I32Type; align = 0; offset = 0l; pack = Some Pack8});
            Plain (Const (I32 (I32.add d 1l) @@ e.at));
            Plain (Const (I32 (I32.add s 1l) @@ e.at));
            Plain (Const (I32 (I32.sub n 1l) @@ e.at));
            Plain (MemoryInit x);
          ]

      | DataDrop x, vs ->
        let seg = data c.frame.inst x in
        seg := "";
        vs, []

      | RefNull t, vs' ->
        Ref (NullRef (sem_heap_type c.frame.inst.types t)) :: vs', []

      | RefFunc x, vs' ->
        let f = func c.frame.inst x in
        Ref (FuncRef f) :: vs', []

      | RefTest NullOp, Ref r :: vs' ->
        value_of_bool (match r with NullRef _ -> true | _ -> false) :: vs', []

      | RefTest I31Op, Ref r :: vs' ->
        value_of_bool (match r with I31.I31Ref _ -> true | _ -> false) :: vs', []

      | RefTest DataOp, Ref r :: vs' ->
        value_of_bool (match r with Data.DataRef _ -> true | _ -> false) :: vs', []

      | RefTest ArrayOp, Ref r :: vs' ->
        value_of_bool (match r with Data.DataRef (Data.Array _) -> true | _ -> false) :: vs', []

      | RefTest FuncOp, Ref r :: vs' ->
        value_of_bool (match r with FuncRef _ -> true | _ -> false) :: vs', []

      | RefTest RttOp, Ref (NullRef _) :: vs' ->
        vs', [Trapping "null RTT reference" @@ e.at]

      | RefTest RttOp, Ref (Rtt.RttRef rtt) :: Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          value_of_bool false :: vs', []
        | Data.DataRef d ->
          value_of_bool (Rtt.match_rtt (Data.read_rtt d) rtt) :: vs', []
        | FuncRef f ->
          value_of_bool (Rtt.match_rtt (Func.read_rtt f) rtt) :: vs', []
        | _ ->
          Crash.error e.at "wrong reference type"
        )

      | RefCast NullOp, Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          vs', [Trapping "null reference" @@ e.at]
        | _ ->
          Ref r :: vs', []
        )

      | RefCast I31Op, Ref r :: vs' ->
        (match r with
        | I31.I31Ref _ ->
          Ref r :: vs', []
        | _ ->
          vs', [Trapping ("cast failure, expected i31 but got " ^
            string_of_value (Ref r)) @@ e.at]
        )

      | RefCast DataOp, Ref r :: vs' ->
        (match r with
        | Data.DataRef _ ->
          Ref r :: vs', []
        | _ ->
          vs', [Trapping ("cast failure, expected data but got " ^
            string_of_value (Ref r)) @@ e.at]
        )

      | RefCast ArrayOp, Ref r :: vs' ->
        (match r with
        | Data.DataRef (Data.Array _) ->
          Ref r :: vs', []
        | _ ->
          vs', [Trapping ("cast failure, expected array but got " ^
            string_of_value (Ref r)) @@ e.at]
        )

      | RefCast FuncOp, Ref r :: vs' ->
        (match r with
        | FuncRef _ ->
          Ref r :: vs', []
        | _ ->
          vs', [Trapping ("cast failure, expected func but got " ^
            string_of_value (Ref r)) @@ e.at]
        )

      | RefCast RttOp, Ref (NullRef _) :: vs' ->
        vs', [Trapping "null RTT reference" @@ e.at]

      | RefCast RttOp, Ref (Rtt.RttRef rtt) :: Ref r :: vs' ->
        (match r with
        | NullRef _ ->
          Ref r :: vs', []
        | Data.DataRef d when Rtt.match_rtt (Data.read_rtt d) rtt ->
          Ref r :: vs', []
        | FuncRef f when Rtt.match_rtt (Func.read_rtt f) rtt ->
          Ref r :: vs', []
        | Data.DataRef d ->
          vs', [Trapping ("cast failure, expected " ^
            Rtt.string_of_rtt rtt ^ " but got " ^
            Rtt.string_of_rtt (Data.read_rtt d)) @@ e.at]
        | FuncRef f ->
          vs', [Trapping ("cast failure, expected " ^
            Rtt.string_of_rtt rtt ^ " but got " ^
            Rtt.string_of_rtt (Func.read_rtt f)) @@ e.at]
        | _ ->
          Crash.error e.at "wrong reference type"
        )

      | RefEq, Ref r1 :: Ref r2 :: vs' ->
        value_of_bool (eq_ref r1 r2) :: vs', []

      | I31New, Num (I32 i) :: vs' ->
        Ref (I31.I31Ref (I31.of_i32 i)) :: vs', []

      | I31Get ext, Ref (I31.I31Ref i) :: vs' ->
        Num (I32 (I31.to_i32 ext i)) :: vs', []

      | StructNew (x, initop), Ref (Rtt.RttRef rtt) :: vs' ->
        let StructType fts = struct_type c.frame.inst x in
        let args, vs'' =
          match initop with
          | Explicit ->
            let args, vs'' = split (List.length fts) vs' e.at in
            List.rev args, vs''
          | Implicit ->
            let ts = List.map unpacked_field_type fts in
            try List.map default_value ts, vs'
            with Failure _ -> Crash.error e.at "non-defaultable type"
        in
        let data = 
          try Data.alloc_struct (type_ c.frame.inst x) rtt args
          with Failure _ -> Crash.error e.at "type mismatch packing value"
        in Ref (Data.DataRef data) :: vs'', []

      | StructGet (x, y, exto), Ref (NullRef _) :: vs' ->
        vs', [Trapping "null structure reference" @@ e.at]

      | StructGet (x, y, exto), Ref Data.(DataRef (Struct (_, _, fs))) :: vs' ->
        let f =
          try Lib.List32.nth fs y.it
          with Failure _ -> Crash.error y.at "undefined field"
        in
        (try Data.read_field f exto :: vs', []
        with Failure _ -> Crash.error e.at "type mismatch reading field")

      | StructSet (x, y), v :: Ref (NullRef _) :: vs' ->
        vs', [Trapping "null structure reference" @@ e.at]

      | StructSet (x, y), v :: Ref Data.(DataRef (Struct (_, _, fs))) :: vs' ->
        let f =
          try Lib.List32.nth fs y.it
          with Failure _ -> Crash.error y.at "undefined field"
        in
        (try Data.write_field f v; vs', []
        with Failure _ -> Crash.error e.at "type mismatch writing field")

      | ArrayNew (x, initop), Ref (Rtt.RttRef rtt) :: Num (I32 n) :: vs' ->
        let ArrayType (FieldType (st, _)) = array_type c.frame.inst x in
        let arg, vs'' =
          match initop with
          | Explicit -> List.hd vs', List.tl vs'
          | Implicit ->
            try default_value (unpacked_storage_type st), vs'
            with Failure _ -> Crash.error e.at "non-defaultable type"
        in
        let data =
          try Data.alloc_array (type_ c.frame.inst x) rtt (Lib.List32.make n arg)
          with Failure _ -> Crash.error e.at "type mismatch packing value"
        in Ref (Data.DataRef data) :: vs'', []

      | ArrayNewFixed (x, n), Ref (Rtt.RttRef rtt) :: vs' ->
        let args, vs'' = split (I32.to_int_u n) vs' e.at in
        let data =
          try Data.alloc_array (type_ c.frame.inst x) rtt (List.rev args)
          with Failure _ -> Crash.error e.at "type mismatch packing value"
        in Ref (Data.DataRef data) :: vs'', []

      | ArrayNewElem (x, y),
        Ref (Rtt.RttRef rtt) :: Num (I32 n) :: Num (I32 s) :: vs' ->
        if elem_oob c.frame y s n then
          vs', [Trapping (table_error e.at Table.Bounds) @@ e.at]
        else
          let seg = elem c.frame.inst y in
          let args =
            List.map (fun r -> Ref r) (Lib.List32.take n (Lib.List32.drop s !seg)) in
          let data =
            try Data.alloc_array (type_ c.frame.inst x) rtt args
            with Failure _ -> Crash.error e.at "type mismatch packing value"
          in Ref (Data.DataRef data) :: vs', []

      | ArrayNewData (x, y),
        Ref (Rtt.RttRef rtt) :: Num (I32 n) :: Num (I32 s) :: vs' ->
        if data_oob c.frame y s n then
          vs', [Trapping (memory_error e.at Memory.Bounds) @@ e.at]
        else
          let ArrayType (FieldType (st, _)) = array_type c.frame.inst x in
          let seg = data c.frame.inst y in
          let bs = Bytes.of_string !seg in
          let args = Lib.List32.init n
            (fun i ->
              let j = I32.to_int_u s + I32.to_int_u i * storage_size st in
              match st with
              | PackedStorageType Pack8 ->
                Num (I32 (I32.of_int_u (Bytes.get_uint8 bs j)))
              | PackedStorageType Pack16 ->
                Num (I32 (I32.of_int_u (Bytes.get_uint16_le bs j)))
              | ValueStorageType (NumType I32Type) ->
                Num (I32 (Bytes.get_int32_le bs j))
              | ValueStorageType (NumType I64Type) ->
                Num (I64 (Bytes.get_int64_le bs j))
              | ValueStorageType (NumType F32Type) ->
                Num (F32 (F32.of_bits (Bytes.get_int32_le bs j)))
              | ValueStorageType (NumType F64Type) ->
                Num (F64 (F64.of_bits (Bytes.get_int64_le bs j)))
              | ValueStorageType (VecType V128Type) ->
                Vec (V128 (V128.of_bits (String.sub !seg j 16)))
              | _ ->
                Crash.error e.at "type mismatch packing value"
            )
          in
          let data =
            try Data.alloc_array (type_ c.frame.inst x) rtt args
            with Failure _ -> Crash.error e.at "type mismatch packing value"
          in Ref (Data.DataRef data) :: vs', []

      | ArrayGet (x, exto), Num (I32 i) :: Ref (NullRef _) :: vs' ->
        vs', [Trapping "null array reference" @@ e.at]

      | ArrayGet (x, exto), Num (I32 i) :: Ref Data.(DataRef (Array (_, _, fs))) :: vs'
        when I32.ge_u i (Lib.List32.length fs) ->
        vs', [Trapping "out of bounds array access" @@ e.at]

      | ArrayGet (x, exto), Num (I32 i) :: Ref Data.(DataRef (Array (_, _, fs))) :: vs' ->
        (try Data.read_field (Lib.List32.nth fs i) exto :: vs', []
        with Failure _ -> Crash.error e.at "type mismatch reading array")

      | ArraySet x, v :: Num (I32 i) :: Ref (NullRef _) :: vs' ->
        vs', [Trapping "null array reference" @@ e.at]

      | ArraySet x, v :: Num (I32 i) :: Ref (Data.DataRef (Data.Array (_, _, fs))) :: vs'
        when I32.ge_u i (Lib.List32.length fs) ->
        vs', [Trapping "out of bounds array access" @@ e.at]

      | ArraySet x, v :: Num (I32 i) :: Ref (Data.DataRef (Data.Array (_, _, fs))) :: vs' ->
        (try Data.write_field (Lib.List32.nth fs i) v; vs', []
        with Failure _ -> Crash.error e.at "type mismatch writing array")

      | ArrayLen, Ref (NullRef _) :: vs' ->
        vs', [Trapping "null array reference" @@ e.at]

      | ArrayLen, Ref (Data.DataRef (Data.Array (_, _, svs))) :: vs' ->
        Num (I32 (Lib.List32.length svs)) :: vs', []

      | RttCanon x, vs ->
        let rtt = Rtt.alloc (type_ c.frame.inst x) in
        Ref (Rtt.RttRef rtt) :: vs, []

      | Const n, vs ->
        Num n.it :: vs, []

      | Test testop, Num n :: vs' ->
        (try value_of_bool (Eval_num.eval_testop testop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | Compare relop, Num n2 :: Num n1 :: vs' ->
        (try value_of_bool (Eval_num.eval_relop relop n1 n2) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | Unary unop, Num n :: vs' ->
        (try Num (Eval_num.eval_unop unop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | Binary binop, Num n2 :: Num n1 :: vs' ->
        (try Num (Eval_num.eval_binop binop n1 n2) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | Convert cvtop, Num n :: vs' ->
        (try Num (Eval_num.eval_cvtop cvtop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecConst v, vs ->
        Vec v.it :: vs, []

      | VecTest testop, Vec n :: vs' ->
        (try value_of_bool (Eval_vec.eval_testop testop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecUnary unop, Vec n :: vs' ->
        (try Vec (Eval_vec.eval_unop unop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecBinary binop, Vec n2 :: Vec n1 :: vs' ->
        (try Vec (Eval_vec.eval_binop binop n1 n2) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecCompare relop, Vec n2 :: Vec n1 :: vs' ->
        (try Vec (Eval_vec.eval_relop relop n1 n2) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecConvert cvtop, Vec n :: vs' ->
        (try Vec (Eval_vec.eval_cvtop cvtop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecShift shiftop, Num s :: Vec v :: vs' ->
        (try Vec (Eval_vec.eval_shiftop shiftop v s) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecBitmask bitmaskop, Vec v :: vs' ->
        (try Num (Eval_vec.eval_bitmaskop bitmaskop v) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecTestBits vtestop, Vec n :: vs' ->
        (try value_of_bool (Eval_vec.eval_vtestop vtestop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecUnaryBits vunop, Vec n :: vs' ->
        (try Vec (Eval_vec.eval_vunop vunop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecBinaryBits vbinop, Vec n2 :: Vec n1 :: vs' ->
        (try Vec (Eval_vec.eval_vbinop vbinop n1 n2) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecTernaryBits vternop, Vec v3 :: Vec v2 :: Vec v1 :: vs' ->
        (try Vec (Eval_vec.eval_vternop vternop v1 v2 v3) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecSplat splatop, Num n :: vs' ->
        (try Vec (Eval_vec.eval_splatop splatop n) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecExtract extractop, Vec v :: vs' ->
        (try Num (Eval_vec.eval_extractop extractop v) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | VecReplace replaceop, Num r :: Vec v :: vs' ->
        (try Vec (Eval_vec.eval_replaceop replaceop v r) :: vs', []
        with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])

      | _ ->
        let s1 = string_of_values (List.rev vs) in
        let s2 = string_of_result_type (List.map type_of_value (List.rev vs)) in
        Crash.error e.at
          ("missing or ill-typed operand on stack (" ^ s1 ^ " : " ^ s2 ^ ")")
      )

    | Refer r, vs ->
      Ref r :: vs, []

    | Trapping msg, vs ->
      assert false

    | Returning _, vs
    | ReturningInvoke _, vs ->
      Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
      Crash.error e.at "undefined label"

    | Label (n, es0, (vs', [])), vs ->
      vs' @ vs, []

    | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es')), vs ->
      take n vs0 e.at @ vs, List.map plain es0

    | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es')), vs ->
      vs, [Breaking (Int32.sub k 1l, vs0) @@ at]

    | Label (n, es0, (vs', e' :: es')), vs when is_jumping e' ->
      vs, [e']

    | Label (n, es0, code'), vs ->
      let c' = step {c with code = code'} in
      vs, [Label (n, es0, c'.code) @@ e.at]

    | Local (n, vs0, (vs', [])), vs ->
      vs' @ vs, []

    | Local (n, vs0, (vs', e' :: es')), vs when is_jumping e' ->
      vs' @ vs, [e']

    | Local (n, vs0, code'), vs ->
      let frame' = {c.frame with locals = List.map ref vs0 @ c.frame.locals} in
      let c' = step {c with frame = frame'; code = code'} in
      let vs0' = List.map (!) (take (List.length vs0) c'.frame.locals e.at) in
      vs, [Local (n, vs0', c'.code) @@ e.at]

    | Frame (n, frame', (vs', [])), vs ->
      vs' @ vs, []

    | Frame (n, frame', (vs', {it = Trapping msg; at} :: es')), vs ->
      vs, [Trapping msg @@ at]

    | Frame (n, frame', (vs', {it = Returning vs0; at} :: es')), vs ->
      take n vs0 e.at @ vs, []

    | Frame (n, frame', (vs', {it = ReturningInvoke (vs0, f); at} :: es')), vs ->
      let FuncType (ts1, _) = Func.type_of f in
      take (List.length ts1) vs0 e.at @ vs, [Invoke f @@ at]

    | Frame (n, frame', code'), vs ->
      let c' = step {frame = frame'; code = code'; budget = c.budget - 1} in
      vs, [Frame (n, frame', c'.code) @@ e.at]

    | Invoke f, vs when c.budget = 0 ->
      Exhaustion.error e.at "call stack exhausted"

    | Invoke f, vs ->
      let FuncType (ts1, ts2) = Func.type_of f in
      let args, vs' = split (List.length ts1) vs e.at in
      (match f with
      | Func.AstFunc (_, inst', func) ->
        let {locals; body; _} = func.it in
        let m = Lib.Promise.value inst' in
        let ts = List.map (fun t -> Types.sem_value_type m.types t.it) locals in
        let vs0 = List.rev args @ List.map default_value ts in
        let locals' = List.map (fun t -> t @@ func.at) ts1 @ locals in
        let st = SubType ([], FuncDefType (FuncType ([], ts2))) in
        let x = Types.alloc_uninit () in
        Types.init x (RecCtxType ([(SemVar x, st)], 0l));
        let bt = VarBlockType (SemVar x) in
        let es0 = [Plain (Let (bt, locals', body)) @@ func.at] in
        vs', [Frame (List.length ts2, frame m, (List.rev vs0, es0)) @@ e.at]

      | Func.HostFunc (_, f) ->
        (try List.rev (f (List.rev args)) @ vs', []
        with Crash (_, msg) -> Crash.error e.at msg)

      | Func.ClosureFunc (_, f', args') ->
        args @ args' @ vs', [Invoke f' @@ e.at]
      )
  in {c with code = vs', es' @ List.tl es}


let rec eval (c : config) : value stack =
  match c.code with
  | vs, [] ->
    vs

  | vs, {it = Trapping msg; at} :: _ ->
    Trap.error at msg

  | vs, es ->
    eval (step c)


(* Functions & Constants *)

let rec at_func = function
 | Func.AstFunc (_, _, f) -> f.at
 | Func.HostFunc _ -> no_region
 | Func.ClosureFunc (_, func, _) -> at_func func

let invoke (func : func_inst) (vs : value list) : value list =
  let at = at_func func in
  let FuncType (ts, _) = Func.type_of func in
  if List.length vs <> List.length ts then
    Crash.error at "wrong number of arguments";
  if not (List.for_all2 (fun v -> Match.match_value_type [] (type_of_value v)) vs ts) then
    Crash.error at "wrong types of arguments";
  let c = config empty_module_inst (List.rev vs) [Invoke func @@ at] in
  try List.rev (eval c) with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

let eval_const (inst : module_inst) (const : const) : value =
  let c = config inst [] (List.map plain const.it) in
  match eval c with
  | [v] -> v
  | vs -> Crash.error const.at "wrong number of results on stack"


(* Modules *)

let create_type (type_ : type_) : type_inst list =
  match type_.it with
  | RecDefType sts -> List.map (fun _ -> Types.alloc_uninit ()) sts

let create_func (inst : module_inst) (f : func) : func_inst =
  Func.alloc (type_ inst f.it.ftype) (Lib.Promise.make ()) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let {ttype} = tab.it in
  let TableType (_lim, (_, t)) as tt = Types.sem_table_type inst.types ttype in
  Table.alloc tt (NullRef t)

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let {mtype} = mem.it in
  Memory.alloc (Types.sem_memory_type inst.types mtype)

let create_global (inst : module_inst) (glob : global) : module_inst =
  let {gtype; ginit} = glob.it in
  let v = eval_const inst ginit in
  let glob = Global.alloc (Types.sem_global_type inst.types gtype) v in
  { inst with globals = inst.globals @ [glob] }

let create_export (inst : module_inst) (ex : export) : export_inst =
  let {name; edesc} = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | GlobalExport x -> ExternGlobal (global inst x)
  in (name, ext)

let create_elem (inst : module_inst) (seg : elem_segment) : elem_inst =
  let {etype; einit; _} = seg.it in
  ref (List.map (fun c -> as_ref (eval_const inst c)) einit)

let create_data (inst : module_inst) (seg : data_segment) : data_inst =
  let {dinit; _} = seg.it in
  ref dinit


let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst)
  : module_inst =
  let it = extern_type_of_import_type (import_type_of m im) in
  let et = Types.sem_extern_type inst.types it in
  let et' = extern_type_of inst.types ext in
  if not (Match.match_extern_type [] et' et) then
    Link.error im.at ("incompatible import type for " ^
      "\"" ^ Utf8.encode im.it.module_name ^ "\" " ^
      "\"" ^ Utf8.encode im.it.item_name ^ "\": " ^
      "expected " ^ Types.string_of_extern_type et ^
      ", got " ^ Types.string_of_extern_type et');
  match ext with
  | ExternFunc func -> {inst with funcs = func :: inst.funcs}
  | ExternTable tab -> {inst with tables = tab :: inst.tables}
  | ExternMemory mem -> {inst with memories = mem :: inst.memories}
  | ExternGlobal glob -> {inst with globals = glob :: inst.globals}


let init_type (inst : module_inst) (x, ts : int32 * type_inst list) (type_ : type_) =
  let cts = ctx_types_of_def_type x type_.it in
  let ts1 = Lib.List.take (List.length cts) ts in
  List.iter2 Types.init ts1 (List.map (Types.sem_ctx_type inst.types) cts);
  Int32.add x (Lib.List32.length cts), Lib.List.drop (List.length cts) ts

let init_func (inst : module_inst) (func : func_inst) =
  match func with
  | Func.AstFunc (_, inst_prom, _) -> Lib.Promise.fulfill inst_prom inst
  | _ -> assert false

let run_elem i elem =
  let at = elem.it.emode.at in
  let x = i @@ at in
  match elem.it.emode.it with
  | Passive -> []
  | Active {index; offset} ->
    offset.it @ [
      Const (I32 0l @@ at) @@ at;
      Const (I32 (Lib.List32.length elem.it.einit) @@ at) @@ at;
      TableInit (index, x) @@ at;
      ElemDrop x @@ at
    ]
  | Declarative ->
    [ElemDrop x @@ at]

let run_data i data =
  let at = data.it.dmode.at in
  let x = i @@ at in
  match data.it.dmode.it with
  | Passive -> []
  | Active {index; offset} ->
    assert (index.it = 0l);
    offset.it @ [
      Const (I32 0l @@ at) @@ at;
      Const (I32 (Int32.of_int (String.length data.it.dinit)) @@ at) @@ at;
      MemoryInit x @@ at;
      DataDrop x @@ at
    ]
  | Declarative -> assert false

let run_start start =
  [Call start @@ start.at]

let init (m : module_) (exts : extern list) : module_inst =
  let
    { imports; tables; memories; globals; funcs; types;
      exports; elems; datas; start
    } = m.it
  in
  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 = {empty_module_inst with types = List.concat_map create_type types} in
  ignore (List.fold_left (init_type inst0) (0l, inst0.types) types);
  let inst1 = List.fold_right2 (add_import m) exts imports inst0 in
  let fs = List.map (create_func inst1) funcs in
  let inst2 = {inst1 with funcs = inst1.funcs @ fs} in
  let inst3 = List.fold_left create_global inst2 globals in
  let inst4 =
    { inst3 with
      tables = inst2.tables @ List.map (create_table inst3) tables;
      memories = inst2.memories @ List.map (create_memory inst3) memories;
    }
  in
  let inst =
    { inst4 with
      exports = List.map (create_export inst4) exports;
      elems = List.map (create_elem inst4) elems;
      datas = List.map (create_data inst4) datas;
    }
  in
  List.iter (init_func inst) fs;
  let es_elem = List.concat (Lib.List32.mapi run_elem elems) in
  let es_data = List.concat (Lib.List32.mapi run_data datas) in
  let es_start = Lib.Option.get (Lib.Option.map run_start start) [] in
  ignore (eval (config inst [] (List.map plain (es_elem @ es_data @ es_start))));
  inst
