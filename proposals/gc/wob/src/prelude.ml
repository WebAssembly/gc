open Source
open Syntax

let pos = {file = "predefined"; line = 0; column = 0}
let at = {left = pos; right = pos}
let region = at

let pre_typs =
  [ "Bool", BoolT;
    "Byte", ByteT;
    "Int", IntT;
    "Float", FloatT;
    "Text", TextT;
    "Object", ObjT;
  ]

let pre_vals =
  [ "null", NullLit;
    "true", BoolLit true;
    "false", BoolLit false;
    "nan", FloatLit nan;
  ]

let prelude =
  List.map (fun (y, t) -> TypD (y @@ at, [], t @@ at) @@ at) pre_typs @
  List.map (fun (x, l) -> LetD (x @@ at, LitE l @@ at) @@ at) pre_vals
