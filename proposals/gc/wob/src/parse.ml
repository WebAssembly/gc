type start = Prog | Repl

exception Error = Syntax.Error

let parser = function
  | Prog -> Parser.prog
  | Repl -> Parser.repl

let parse name lexbuf start =
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name};
  try parser start Lexer.token lexbuf
  with Error (region, s) ->
    let region' = if region <> Source.no_region then region else
      {Source.left = Lexer.convert_pos lexbuf.Lexing.lex_start_p;
       Source.right = Lexer.convert_pos lexbuf.Lexing.lex_curr_p} in
    raise (Error (region', s))

let prog_of_string s =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Prog
