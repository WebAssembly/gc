(* WebAssembly-compatible obj implementation *)

module type ObjType =
sig
    type t = { type_index : int32; }
  val zero : t

  val to_string : t -> string
  val of_string : string -> t

  val get_type_index : t -> int32
end

module Obj =
  struct
    type t = { type_index : int32; }

    let init ty = {
        type_index = ty
    }

    let zero = init Int32.zero

    let to_string o = "{"
        ^ "type_index:" ^ (Int32.to_string o.type_index)
        ^ "}"
    let of_string s =
        init (Int32.of_int(int_of_string s))

    let get_type_index o = o.type_index
  end
