open Source
open Syntax

let pos = {file = "predefined"; line = 0; column = 0}
let region = {left = pos; right = pos}

let typs =
  [ "Bool", BoolT;
    "Byte", ByteT;
    "Int", IntT;
    "Float", FloatT;
    "Text", TextT;
  ]

let vals =
  [ "nan", FloatL nan;
    "True", BoolL true;
    "False", BoolL false;
  ]
