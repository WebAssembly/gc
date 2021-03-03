%{
open Source
open Syntax


(* Error handling *)

let error at msg = raise (Syntax.Error (at, msg))

let parse_error msg =
  error no_region (if msg = "syntax error" then "unexpected token" else msg)


(* Position handling *)

let position_to_pos position =
  { file = position.Lexing.pos_fname;
    line = position.Lexing.pos_lnum;
    column = position.Lexing.pos_cnum - position.Lexing.pos_bol
  }

let positions_to_region position1 position2 =
  { left = position_to_pos position1;
    right = position_to_pos position2
  }

let at () =
  positions_to_region (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())
let ati i =
  positions_to_region (Parsing.rhs_start_pos i) (Parsing.rhs_end_pos i)


(* Literals *)

let nat s at =
  try
    let n = int_of_string s in
    if n >= 0 then n else raise (Failure "")
  with Failure _ -> error at "integer constant out of range"

let int s at =
  try Int32.of_string s with Failure _ -> error at "int constant out of range"

let float s at =
  try float_of_string s with Failure _ -> error at "float constant out of range"

%}

%token EOF

%token LPAR RPAR LBRACK RBRACK LCURLY RCURLY COMMA SEMICOLON SEMICOLON_EOL
%token COLON EQ LT GT ARROW ASSIGN SUB SUP DOT
%token EQOP NEOP LEOP LTOP GTOP GEOP
%token ADDOP SUBOP MULOP DIVOP MODOP ANDOP OROP NOTOP CATOP
%token NEW IF ELSE WHILE RETURN ASSERT
%token LET VAR FUNC TYPE CLASS IMPORT FROM
%token<string> NAT
%token<string> FLOAT
%token<string> TEXT
%token<string> ID

%nonassoc RETURN_NO_ARG IF_NO_ELSE
%nonassoc ELSE WHILE

%right ASSIGN
%left OROP
%left ANDOP
%nonassoc EQOP NEOP LTOP GTOP LEOP GEOP
%left COLON SUP
%left ADDOP SUBOP CATOP
%left MULOP DIVOP MODOP

%start prog repl
%type<Syntax.prog> prog
%type<Syntax.prog> repl

%%


/* Variables */

var :
  | ID { $1 @@ at () }

var_list :
  | /* empty */ { [] }
  | var { [$1] }
  | var COMMA var_list { $1 :: $3 }


/* Types */

typ_simple :
  | var {
      (match $1.it with
      | "Bool" -> BoolT
      | "Byte" -> ByteT
      | "Int" -> IntT
      | "Float" -> FloatT
      | "Text" -> TextT
      | "Object" -> ObjT
      | _ -> VarT ($1, [])
      ) @@ at ()
    }
  | var LT typ_list GT { VarT ($1, $3) @@ at () }

typ_tup :
  | LPAR typ_list RPAR { match $2 with [t] -> t | ts -> TupT ts @@ at () }

typ_param :
  | typ_simple { [$1] }
  | typ_tup { match $1.it with TupT ts -> ts | _ -> [$1] }

typ_post :
  | typ_simple { $1 }
  | typ_tup { $1 }
  | typ_post LBRACK RBRACK { ArrayT $1 @@ at () }

typ :
  | typ_post { $1 }
  | typ_param ARROW typ { FuncT ([], $1, $3) @@ at () }
  | LT var_list GT typ_tup ARROW typ {
      FuncT ($2, (match $4.it with TupT ts -> ts | _ -> [$4]), $6) @@ at ()
    }

typ_list :
  | /* empty */ { [] }
  | typ { [$1] }
  | typ COMMA typ_list { $1 :: $3 }


/* Expressions */

lit :
  | NAT { IntLit (int $1 (at ())) }
  | FLOAT { FloatLit (float $1 (at ())) }
  | TEXT { TextLit $1 }

exp_block :
  | LCURLY dec_list RCURLY { BlockE $2 @@ at () }

exp_simple :
  | exp_block { $1 }
  | var {
      (match $1.it with
      | "null" -> LitE NullLit
      | "true" -> LitE (BoolLit true)
      | "false" -> LitE (BoolLit false)
      | "nan" -> LitE (FloatLit nan)
      | _ -> VarE $1
      ) @@ $1.at
    }
  | lit { LitE $1 @@ at () }
  | LBRACK exp_list RBRACK { ArrayE $2 @@ at () }

exp_tup :
  | LPAR exp_list RPAR { match $2 with [e] -> e | es -> TupE es @@ at () }

exp_arg :
  | exp_tup { match $1.it with TupE es -> es | e -> [$1] }

exp_post :
  | exp_simple { $1 }
  | exp_tup { $1 }
  | exp_post LBRACK exp RBRACK { IdxE ($1, $3) @@ at () }
  | exp_post DOT NAT { ProjE ($1, nat $3 (ati 3)) @@ at () }
  | exp_post DOT var { DotE ($1, $3) @@ at () }
  | exp_post exp_arg { CallE ($1, [], $2) @@ at () }
  | exp_post LT typ_list GT exp_arg { CallE ($1, $3, $5) @@ at () }

exp_un :
  | exp_post { $1 }
  | ADDOP exp_un { UnE (PosOp, $2) @@ at () }
  | SUBOP exp_un { UnE (NegOp, $2) @@ at () }
  | NOTOP exp_un { UnE (NotOp, $2) @@ at () }
  | NEW var exp_arg { NewE ($2, [], $3) @@ at () }
  | NEW var LT typ_list GT exp_arg { NewE ($2, $4, $6) @@ at () }
  | NEW typ_post LBRACK exp RBRACK LPAR exp RPAR {
      NewArrayE ($2, $4, $7) @@ at ()
    }

exp_bin :
  | exp_un { $1 }
  | exp_bin ADDOP exp_bin { BinE ($1, AddOp, $3) @@ at () }
  | exp_bin SUBOP exp_bin { BinE ($1, SubOp, $3) @@ at () }
  | exp_bin MULOP exp_bin { BinE ($1, MulOp, $3) @@ at () }
  | exp_bin DIVOP exp_bin { BinE ($1, DivOp, $3) @@ at () }
  | exp_bin MODOP exp_bin { BinE ($1, ModOp, $3) @@ at () }
  | exp_bin ANDOP exp_bin { BinE ($1, AndOp, $3) @@ at () }
  | exp_bin OROP  exp_bin { BinE ($1, OrOp,  $3) @@ at () }
  | exp_bin CATOP exp_bin { BinE ($1, CatOp, $3) @@ at () }
  | exp_bin EQOP exp_bin { RelE ($1, EqOp, $3) @@ at () }
  | exp_bin NEOP exp_bin { RelE ($1, NeOp, $3) @@ at () }
  | exp_bin LTOP exp_bin { RelE ($1, LtOp, $3) @@ at () }
  | exp_bin GTOP exp_bin { RelE ($1, GtOp, $3) @@ at () }
  | exp_bin LEOP exp_bin { RelE ($1, LeOp, $3) @@ at () }
  | exp_bin GEOP exp_bin { RelE ($1, GeOp, $3) @@ at () }
  | exp_bin COLON typ { AnnotE ($1, $3) @@ at () }
  | exp_bin SUP typ { CastE ($1, $3) @@ at () }
  | exp_bin ASSIGN exp_bin { AssignE ($1, $3) @@ at () }

exp :
  | exp_bin { $1 }
  | RETURN %prec RETURN_NO_ARG { RetE (TupE [] @@ at ()) @@ at () }
  | RETURN exp_bin { RetE $2 @@ at () }
  | ASSERT exp_bin { AssertE $2 @@ at () }
  | IF exp_bin exp_block %prec IF_NO_ELSE { IfE ($2, $3, TupE [] @@ at ()) @@ at () }
  | IF exp_bin exp_block ELSE exp_block { IfE ($2, $3, $5) @@ at () }
  | WHILE exp_bin exp_block { WhileE ($2, $3) @@ at () }
  | FUNC gen_opt LPAR param_list RPAR exp {
      BlockE [
        FuncD ("it" @@ at (), $2, $4, TupT [] @@ ati 1, $6) @@ at ();
        ExpD (VarE ("it" @@ at ()) @@ at ()) @@ at ();
      ] @@ at ()
    }
  | FUNC gen_opt LPAR param_list RPAR COLON typ exp_block {
      BlockE [
        FuncD ("it" @@ at (), $2, $4, $7, $8) @@ at ();
        ExpD (VarE ("it" @@ at ()) @@ at ()) @@ at ();
      ] @@ at ()
    }
  | CLASS gen_opt LPAR param_list RPAR sup_opt LCURLY dec_list RCURLY {
      BlockE [
        ClassD ("it" @@ at (), $2, $4, $6, $8) @@ at ();
        ExpD (VarE ("it" @@ at ()) @@ at ()) @@ at ();
      ] @@ at ()
    }

exp_list :
  | /* empty */ { [] }
  | exp { [$1] }
  | exp COMMA exp_list { $1 :: $3 }


/* Declarations */

param :
  | var COLON typ { ($1, $3) }

param_list :
  | /* empty */ { [] }
  | param { [$1] }
  | param COMMA param_list { $1 :: $3 }

gen_opt :
  | /* empty */ { [] }
  | LT var_list GT { $2 }

sup_opt :
  | /* empty */ { None }
  | SUB var LPAR exp_list RPAR { Some ($2, [], $4) }
  | SUB var LT typ_list GT LPAR exp_list RPAR { Some ($2, $4, $7) }

dec :
  | exp { ExpD $1 @@ at () }
  | LET var EQ exp { LetD ($2, $4) @@ at () }
  | LET var COLON typ EQ exp { LetD ($2, AnnotE ($6, $4) @@ at ()) @@ at () }
  | VAR var COLON typ EQ exp { VarD ($2, $4, $6) @@ at () }
  | TYPE var EQ typ { TypD ($2, [], $4) @@ at () }
  | TYPE var LT var_list GT EQ typ { TypD ($2, $4, $7) @@ at () }
  | FUNC var gen_opt LPAR param_list RPAR exp_block {
      FuncD ($2, $3, $5, TupT [] @@ ati 1, $7) @@ at ()
    }
  | FUNC var gen_opt LPAR param_list RPAR COLON typ exp_block {
      FuncD ($2, $3, $5, $8, $9) @@ at ()
    }
  | CLASS var gen_opt LPAR param_list RPAR sup_opt LCURLY dec_list RCURLY {
      ClassD ($2, $3, $5, $7, $9) @@ at ()
    }
  | IMPORT var_list FROM TEXT { ImportD ($2, $4) @@ at () }

dec_list :
  | /* empty */ { [] }
  | dec { [$1] }
  | dec SEMICOLON dec_list { $1 :: $3 }
  | dec SEMICOLON_EOL dec_list { $1 :: $3 }

dec_list_noeol :
  | /* empty */ { [] }
  | dec { [$1] }
  | dec SEMICOLON dec_list_noeol { $1 :: $3 }


/* Programs */

prog :
  | dec_list EOF { Prog $1 @@ at () }

repl :
  | dec_list_noeol SEMICOLON_EOL { Prog $1 @@ at () }
