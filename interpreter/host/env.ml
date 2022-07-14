(*
 * Emulation of (a subset of) the `env` module currently used by Binaryen,
 * so that we can run modules generated by Binaryen. This is a stopgap until
 * we have agreement on what libc should look like.
 *)

open Types
open Value
open Instance


let error msg = raise (Eval.Crash (Source.no_region, msg))

let type_error v t =
  error
    ("type error, expected " ^ string_of_value_type t ^
     ", got " ^ string_of_value_type (type_of_value v))

let empty = function
  | [] -> ()
  | vs -> error "type error, too many arguments"

let single = function
  | [] -> error "type error, missing arguments"
  | [v] -> v
  | vs -> error "type error, too many arguments"

let int = function
  | Num (I32 i) -> Int32.to_int i
  | v -> type_error v (NumType I32Type)


let abort vs =
  empty vs;
  print_endline "Abort!";
  exit (-1)

let exit vs =
  exit (int (single vs))


let alloc_func f x =
  ExternFunc (Func.alloc_host (as_sem_var x) f)

let lookup name et =
  match Utf8.encode name, et with
  | "abort", ExternFuncType x -> alloc_func abort x
  | "exit", ExternFuncType x -> alloc_func exit x
  | _ -> raise Not_found
