(* Simple Type Fuzzer *)

module T = Types

let rec fuzz_list k fuzz x y =
  fuzz_list' fuzz x y [] ((1 + Random.int k) * Random.int k)
and fuzz_list' fuzz x y dts = function
  | 0 -> dts
  | i -> fuzz_list' fuzz x y (fuzz x y :: dts) (i - 1)

let rec fuzz n =
  let y = ref 0 in
  Array.init n (fun x ->
    if !y < x && Random.int 5 = 0 then
      y := x + (1 + Random.int 40) * Random.int 40 + 1;
    fuzz_def x (min n (max x !y))
  )

and fuzz_def x y =
  match Random.int 3 with
  | 0 -> T.StructDefType (T.StructType (fuzz_list 5 fuzz_field x y))
  | 1 -> T.ArrayDefType (T.ArrayType (fuzz_field x y))
  | _ -> T.FuncDefType (T.FuncType
      (fuzz_list 3 fuzz_val x y, fuzz_list 2 fuzz_val x y))

and fuzz_field x y =
  T.FieldType (fuzz_storage x y,
    if Random.bool () then T.Mutable else T.Immutable)

and fuzz_storage x y =
  match Random.int 10 with
  | 0 -> T.PackedStorageType T.Pack8
  | 1 -> T.PackedStorageType T.Pack16
  | _ -> T.ValueStorageType (fuzz_val x y)

and fuzz_val x y =
  match Random.int 15 with
  | 0 -> T.NumType T.I32Type
  | 1 -> T.NumType T.I64Type
  | 2 -> T.NumType T.F32Type
  | 3 -> T.NumType T.F64Type
  | _ -> T.RefType
      ((if Random.bool () then T.Nullable else T.NonNullable), fuzz_heap x y)

and fuzz_heap x y =
  match Random.int 100 with
  | 0 -> T.AnyHeapType
  | 1 -> T.EqHeapType
  | 2 -> T.I31HeapType
  | 3 -> T.DataHeapType
  | 4 -> T.FuncHeapType
  | 5 -> T.ExternHeapType
  | 6 | 7 -> T.RttHeapType (fuzz_var x y, None)
  | 8 | 9 -> T.RttHeapType (fuzz_var x y, Some (Int32.of_int (Random.int 4)))
  | _ -> T.DefHeapType (fuzz_var x y)

and fuzz_var x y =
  let idx = Random.(if bool () || x = y then int (x + 1) else x + int (y - x)) in
  T.SynVar (Int32.of_int idx)
