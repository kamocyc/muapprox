{
  exception SyntaxError of string
  open Ast.Logic
  open Lexing

  let update_loc (lexbuf: Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
    
  let int_of_string' s =
    Str.global_replace (Str.regexp "_") "" s
    |> int_of_string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012']+     { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { update_loc lexbuf; main lexbuf }
| "/*" { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "true" { HesParsing.TRUE }
| "false" { HesParsing.FALSE }
| "int" { HesParsing.INT }
| "bool" { HesParsing.BOOL }
| "real" { HesParsing.REAL }
| "=mu" { HesParsing.EQFIX Predicate.Mu }
| "=nu" { HesParsing.EQFIX Predicate.Nu }
| "/\\" { HesParsing.AND }
| "\\/" { HesParsing.OR }
| "!" | "not" { HesParsing.NOT }
| "<=>" { HesParsing.IFF }
| "=>" { HesParsing.IMPLY }
| "-" { HesParsing.MINUS }
| "+" { HesParsing.ADD }
| "*" { HesParsing.MULT }
| "/" { HesParsing.DIV }
| "%" { HesParsing.MOD }
| ">=" { HesParsing.PREDSYM T_int.Geq }
| ">" { HesParsing.PREDSYM T_int.Gt }
| "<=" { HesParsing.PREDSYM T_int.Leq }
| "<" { HesParsing.PREDSYM T_int.Lt }
| "=" { HesParsing.PREDSYM T_bool.Eq }
| "!=" { HesParsing.PREDSYM T_bool.Neq }
| ":" { HesParsing.CORON }
| ";" { HesParsing.SEMI }
| "forall" { HesParsing.BINDER Forall }
| "exists" { HesParsing.BINDER Exists }
| "s.t." | "where" { HesParsing.WHERE }
| "." { HesParsing.DOT }
| "(" { HesParsing.LPAREN }
| ")" { HesParsing.RPAREN }

| ['a'-'z''A'-'Z''#']['a'-'z''A'-'Z''0'-'9'''''_''#']*
    {
      let str = Lexing.lexeme lexbuf in
      HesParsing.ID str
    }
| ('0'|['1'-'9']['0'-'9''_']*)
    {
      let str = Lexing.lexeme lexbuf in
      HesParsing.INTL (int_of_string' str)
    }

| eof { HesParsing.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { update_loc lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
| eof {
    raise
      (SyntaxError
        (Printf.sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }
