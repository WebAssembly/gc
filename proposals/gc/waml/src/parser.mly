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

let int s at =
  try Int32.of_string s with Failure _ -> error at "int constant out of range"

let float s at =
  try float_of_string s with Failure _ -> error at "float constant out of range"

%}

%token EOF

%token LPAR RPAR LBRACK RBRACK LCURLY RCURLY BAR COMMA SEMICOLON SEMICOLON_EOL
%token COLON EQ ARROW DARROW REF DEREF ASSIGN DOT WILD PACK UNPACK
%token EQOP NEOP LEOP LTOP GTOP GEOP
%token ADDOP SUBOP MULOP DIVOP MODOP ANDOP OROP XOROP SHLOP SHROP CATOP CONS
%token ANDTHENOP ORELSEOP NOTOP
%token FUN IF THEN ELSE CASE OF LET IN
%token DO ASSERT VAL TYPE DATA MODULE SIGNATURE WITH REC AND INCLUDE IMPORT FROM
%token<string> NAT FLOAT TEXT LID UID

%nonassoc IF_NO_ELSE
%nonassoc ELSE
%right BAR

%right ARROW
%right ASSIGN
%left ORELSEOP
%left ANDTHENOP
%nonassoc EQOP NEOP LTOP GTOP LEOP GEOP
%left COLON
%right CONS
%left ADDOP SUBOP CATOP
%left OROP
%left ANDOP XOROP
%left MULOP DIVOP MODOP
%nonassoc SHLOP SHROP

%start prog repl
%type<Syntax.prog> prog
%type<Syntax.prog> repl

%%


/* Variables and Paths */

lvar :
  | LID { $1 @@ at () }

uvar :
  | UID { $1 @@ at () }

lpath :
  | lvar { PlainP $1 }
  | mpath DOT lvar { QualP ($1, $3) }

upath :
  | uvar { PlainP $1 }
  | mpath DOT uvar { QualP ($1, $3) }

vvar : lvar { $1 }
tvar : lvar { $1 }
mvar : uvar { $1 }

vcon : uvar { $1 }
tcon : uvar { $1 }
scon : uvar { $1 }

vpath : lpath { $1 @@ at () }
cpath : upath { $1 @@ at () }
tpath : upath { $1 @@ at () }
mpath : upath { $1 @@ at () }
spath : upath { $1 @@ at () }

tvar_seq :
  | /* empty */ { [] }
  | tvar tvar_seq { $1 :: $2 }


/* Types */

typ_simple :
  | tvar { VarT $1 @@ at () }
  | tpath { ConT ($1, []) @@ at () }
  | LPAR typ_list RPAR { match $2 with [t] -> t | ts -> TupT ts @@ at () }

typ_post :
  | typ_simple { $1 }
  | tpath typ_simple_seq1 { ConT ($1, $2) @@ at () }

typ_bin :
  | typ_post { $1 }
  | typ_bin ARROW typ_bin { FunT ($1, $3) @@ at () }

typ :
  | typ_bin { $1 }
  | PACK sig_ { PackT $2 @@ at () }

typ_simple_seq1 :
  | typ_simple { [$1] }
  | typ_simple typ_simple_seq1 { $1 :: $2 }

typ_list :
  | /* empty */ { [] }
  | typ { [$1] }
  | typ COMMA typ_list { $1 :: $3 }


/* Patterns */

lit :
  | NAT { IntL (int $1 (at ())) }
  | FLOAT { FloatL (float $1 (at ())) }
  | TEXT { TextL $1 }

pat_simple :
  | WILD { WildP @@ at () }
  | lit { LitP $1 @@ at () }
  | vvar { VarP $1 @@ at () }
  | cpath { ConP ($1, []) @@ at () }
  | LPAR pat_list RPAR { match $2 with [p] -> p | ps -> TupP ps @@ at () }
  | LBRACK pat_list RBRACK {
      List.fold_right (fun p1 p2 ->
        ConP (PlainP ("Cons" @@ ati 1) @@ ati 1, [p1; p2]) @@ span p1.at p2.at
      ) $2 (ConP (PlainP ("Nil" @@ ati 3) @@ ati 3, []) @@ ati 3)
    }

pat_post :
  | pat_simple { $1 }
  | cpath pat_simple_seq1 { ConP ($1, $2) @@ at () }
  | REF pat_simple { RefP $2 @@ at () }

pat_un :
  | pat_post { $1 }

pat_bin :
  | pat_un { $1 }
  | pat_bin CONS pat_bin {
      ConP (PlainP ("Cons" @@ ati 2) @@ ati 2, [$1; $3]) @@ span $1.at $3.at
    }
  | pat_bin COLON typ { AnnotP ($1, $3) @@ at () }

pat :
  | pat_bin { $1 }

pat_simple_seq1 :
  | pat_simple { [$1] }
  | pat_simple pat_simple_seq1 { $1 :: $2 }

pat_list :
  | /* empty */ { [] }
  | pat { [$1] }
  | pat COMMA pat_list { $1 :: $3 }


/* Expressions */

exp_simple :
  | lit { LitE $1 @@ at () }
  | vpath { VarE $1 @@ at () }
  | cpath { ConE $1 @@ at () }
  | LPAR exp_list RPAR { match $2 with [e] -> e | es -> TupE es @@ at () }
  | LPAR dec_list_nonempty RPAR { LetE ($2, TupE [] @@ at ()) @@ at () }
  | LBRACK exp_list RBRACK {
      List.fold_right (fun e1 e2 ->
        AppE (
          AppE (
            ConE (PlainP ("Cons" @@ ati 1) @@ ati 1) @@ ati 1,
            e1
          ) @@ e1.at,
          e2
        ) @@ span e1.at e2.at
      ) $2 (ConE (PlainP ("Nil" @@ ati 3) @@ ati 3) @@ ati 3)
    }

exp_post :
  | exp_simple { $1 }
  | exp_post DEREF { DerefE $1 @@ at () }
  | exp_post exp_simple { AppE ($1, $2) @@ at () }

exp_un :
  | exp_post { $1 }
  | ADDOP exp_un { UnE (PosOp, $2) @@ at () }
  | SUBOP exp_un { UnE (NegOp, $2) @@ at () }
  | XOROP exp_un { UnE (InvOp, $2) @@ at () }
  | NOTOP exp_un { UnE (NotOp, $2) @@ at () }
  | REF exp_un { RefE $2 @@ at () }

exp_bin :
  | exp_un { $1 }
  | exp_bin ADDOP exp_bin { BinE ($1, AddOp, $3) @@ at () }
  | exp_bin SUBOP exp_bin { BinE ($1, SubOp, $3) @@ at () }
  | exp_bin MULOP exp_bin { BinE ($1, MulOp, $3) @@ at () }
  | exp_bin DIVOP exp_bin { BinE ($1, DivOp, $3) @@ at () }
  | exp_bin MODOP exp_bin { BinE ($1, ModOp, $3) @@ at () }
  | exp_bin ANDOP exp_bin { BinE ($1, AndOp, $3) @@ at () }
  | exp_bin OROP  exp_bin { BinE ($1, OrOp,  $3) @@ at () }
  | exp_bin XOROP exp_bin { BinE ($1, XorOp, $3) @@ at () }
  | exp_bin SHLOP exp_bin { BinE ($1, ShlOp,  $3) @@ at () }
  | exp_bin SHROP exp_bin { BinE ($1, ShrOp, $3) @@ at () }
  | exp_bin CATOP exp_bin { BinE ($1, CatOp, $3) @@ at () }
  | exp_bin EQOP exp_bin { RelE ($1, EqOp, $3) @@ at () }
  | exp_bin NEOP exp_bin { RelE ($1, NeOp, $3) @@ at () }
  | exp_bin LTOP exp_bin { RelE ($1, LtOp, $3) @@ at () }
  | exp_bin GTOP exp_bin { RelE ($1, GtOp, $3) @@ at () }
  | exp_bin LEOP exp_bin { RelE ($1, LeOp, $3) @@ at () }
  | exp_bin GEOP exp_bin { RelE ($1, GeOp, $3) @@ at () }
  | exp_bin ANDTHENOP exp_bin { LogE ($1, AndThenOp, $3) @@ at () }
  | exp_bin ORELSEOP  exp_bin { LogE ($1, OrElseOp,  $3) @@ at () }
  | exp_bin CONS exp_bin {
      AppE (
        AppE (
          ConE (PlainP ("Cons" @@ ati 2) @@ ati 2) @@ ati 2,
          $1
        ) @@ span $1.at (ati 2),
        $3
      ) @@ span $1.at $3.at
    }
  | exp_bin ASSIGN exp_bin { AssignE ($1, $3) @@ at () }
  | exp_bin COLON typ { AnnotE ($1, $3) @@ at () }

exp :
  | exp_bin { $1 }
  | FUN pat_simple_seq1 DARROW exp {
      List.fold_right (fun p1 e2 ->
        FunE (p1, e2) @@ span p1.at e2.at
      ) $2 $4
    }
  | IF exp THEN exp ELSE exp { IfE ($2, $4, $6) @@ at () }
  | IF exp THEN exp %prec IF_NO_ELSE {
      IfE ($2, $4, TupE [] @@ at ()) @@ at ()
    }
  | CASE exp OF case_list %prec BAR { CaseE ($2, $4) @@ at () }
  | PACK mod_post COLON sig_ { PackE ($2, $4) @@ at () }
  | LET dec_list IN exp { LetE ($2, $4) @@ at () }

exp_list :
  | /* empty */ { [] }
  | exp { [$1] }
  | exp COMMA exp_list { $1 :: $3 }

case :
  | pat DARROW exp { ($1, $3) }

case_list :
  | case { [$1] }
  | BAR case { [$2] }
  | case_list BAR case { $1 @ [$3] }


/* Declarations */

con :
  | vcon { ($1, []) @@ at () }
  | vcon typ_simple_seq1 { ($1, $2) @@ at () }

con_list :
  | /* empty */ { [] }
  | con { [$1] }
  | con_list BAR con { $1 @ [$3] }

param :
  | LPAR mvar COLON sig_ RPAR { ($2, $4) }

param_seq :
  | /* empty */ { [] }
  | param param_seq { $1 :: $2 }

bind :
  | VAL pat EQ exp { ValD ($2, $4) @@ at () }
  | VAL vvar pat_simple_seq1 EQ exp {
      ValD (
        VarP $2 @@ ati 1,
        List.fold_right (fun p1 e2 ->
          FunE (p1, e2) @@ span p1.at e2.at
        ) $3 $5
      ) @@ at ()
    }
  | VAL vvar pat_simple_seq1 COLON typ EQ exp {
      ValD (
        VarP $2 @@ ati 1,
        List.fold_right (fun p1 e2 ->
          FunE (p1, e2) @@ span p1.at e2.at
        ) $3 (AnnotE ($7, $5) @@ span $5.at $7.at)
      ) @@ at ()
    }
  | TYPE tcon tvar_seq EQ typ { TypD ($2, $3, $5) @@ at () }
  | DATA tcon tvar_seq EQ con_list { DatD ($2, $3, $5) @@ at () }
  | MODULE mvar param_seq EQ mod_ {
      ModD (
        $2,
        List.fold_right (fun (x, s) m ->
          FunM (x, s, m) @@ span x.at m.at
        ) $3 $5
      ) @@ at ()
    }
  | MODULE mvar param_seq COLON sig_ EQ mod_ {
      ModD (
        $2,
        List.fold_right (fun (x, s) m ->
          FunM (x, s, m) @@ span x.at m.at
        ) $3 (AnnotM ($7, $5) @@ span $5.at $7.at)
      ) @@ at ()
    }
  | SIGNATURE scon EQ sig_ { SigD ($2, $4) @@ at () }
  | INCLUDE mod_ { InclD $2 @@ at () }

bind_list :
  | bind { [$1] }
  | bind AND bind_list { $1 :: $3 }

dec_no_exp :
  | DO exp { ExpD $2 @@ at () }
  | ASSERT exp { AssertD $2 @@ at () }
  | bind { $1 }
  | REC bind_list {
      ignore (List.fold_left (fun sofar d ->
        match d.it with
        | ValD (_, {it = FunE _; _}) when sofar <> `Dat -> `Val
        | DatD _ when sofar <> `Val -> `Dat
        | ValD _ | DatD _ ->
          error d.at "inconsistent declaration inside recursive group"
        | _ -> error d.at "invalid declaration inside recursive group"
      ) `Neither $2);
      RecD $2 @@ at ()
    }

dec :
  | dec_no_exp { $1 }
  | exp { ExpD $1 @@ at () }

dec_no_exp_list :
  | /* empty */ { [] }
  | dec_no_exp dec_no_exp_list { $1 :: $2 }
  | dec_no_exp SEMICOLON dec_list { $1 :: $3 }
  | dec_no_exp SEMICOLON_EOL dec_list { $1 :: $3 }

dec_list :
  | /* empty */ { [] }
  | dec dec_no_exp_list { $1 :: $2 }
  | dec SEMICOLON dec_list { $1 :: $3 }
  | dec SEMICOLON_EOL dec_list { $1 :: $3 }

dec_list_nonempty :
  | dec_no_exp dec_no_exp_list { $1 :: $2 }
  | exp SEMICOLON dec_list { (ExpD $1 @@ ati 1) :: $3 }
  | exp SEMICOLON_EOL dec_list { (ExpD $1 @@ ati 1) :: $3 }

dec_no_exp_list_noeol :
  | /* empty */ { [] }
  | dec_no_exp dec_no_exp_list_noeol { $1 :: $2 }
  | dec_no_exp SEMICOLON dec_list_noeol { $1 :: $3 }

dec_list_noeol :
  | /* empty */ { [] }
  | dec dec_no_exp_list_noeol { $1 :: $2 }
  | dec SEMICOLON dec_list_noeol { $1 :: $3 }


/* Signatures */

desc :
  | VAL vvar COLON tvar_seq DOT typ { ValS ($2, $4, $6) @@ at () }
  | VAL vvar COLON typ { ValS ($2, [], $4) @@ at () }
  | TYPE tcon tvar_seq EQ typ { TypS ($2, $3, Some $5) @@ at () }
  | TYPE tcon tvar_seq { TypS ($2, $3, None) @@ at () }
  | DATA tcon tvar_seq EQ con_list { DatS ($2, $3, $5) @@ at () }
  | MODULE mvar COLON sig_ { ModS ($2 ,$4) @@ at () }
  | SIGNATURE scon EQ sig_ { SigS ($2, $4) @@ at () }
  | INCLUDE sig_ { InclS $2 @@ at () }

desc_list :
  | desc { [$1] }
  | desc AND desc_list { $1 :: $3 }

spec :
  | desc { $1 }
  | REC desc_list {
      List.iter (fun s ->
        match s.it with
        | DatS _ -> ()
        | _ -> error s.at "invalid declaration inside recursive group"
      ) $2;
      RecS $2 @@ at ()
    }

spec_list :
  | /* empty */ { [] }
  | spec spec_list { $1 :: $2 }
  | spec SEMICOLON spec_list { $1 :: $3 }
  | spec SEMICOLON_EOL spec_list { $1 :: $3 }


sig_simple :
  | spath { ConS $1 @@ at () }
  | LCURLY spec_list RCURLY { StrS $2 @@ at () }
  | LPAR sig_ RPAR { $2 }

sig_ :
  | sig_simple { $1 }
  | LPAR mvar COLON sig_ RPAR ARROW sig_ { FunS ($2, $4, $7) @@ at () }
  | sig_simple ARROW sig_ { FunS ("_" @@ ati 1, $1, $3) @@ at () }
  | sig_simple WITH TYPE tpath tvar_seq EQ typ { WithS ($1, $4, $5, $7) @@ at () }


/* Modules */

mod_simple :
  | mpath { VarM $1 @@ at () }
  | LCURLY dec_list RCURLY { StrM $2 @@ at () }

mod_post :
  | mod_simple { $1 }
  | mod_post mod_simple { AppM ($1, $2) @@ at () }

mod_bin :
  | mod_post { $1 }
  | mod_post COLON sig_ { AnnotM ($1, $3) @@ at () }

mod_ :
  | mod_bin { $1 }
  | FUN LPAR mvar COLON sig_ RPAR DARROW mod_ { FunM ($3, $5, $8) @@ at () }
  | UNPACK exp_post COLON sig_ { UnpackM ($2, $4) @@ at () }
  | LET dec_list IN mod_ { LetM ($2, $4) @@ at () }


/* Programs */

imp :
  | IMPORT mvar FROM TEXT { ImpD ($2, $4) @@ at () }

imp_list :
  | /* empty */ { [] }
  | imp imp_list { $1 :: $2 }
  | imp SEMICOLON imp_list { $1 :: $3 }
  | imp SEMICOLON_EOL imp_list { $1 :: $3 }

imp_list_noeol :
  | /* empty */ { [] }
  | imp imp_list_noeol { $1 :: $2 }
  | imp SEMICOLON imp_list_noeol { $1 :: $3 }

prog :
  | imp_list dec_list EOF { Prog ($1, $2) @@ at () }

repl :
  | imp_list_noeol dec_list_noeol SEMICOLON_EOL {
      Prog ($1, $2) @@ at ()
    }
