
{
open Parser
let line_no = ref 1
let end_of_previousline = ref 0
}

let space = [' ']
let newline = ['\t' '\n' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let upper = ['A'-'Z']
let alphanum = ['0'-'9' 'a'-'z' 'A'-'Z' '_']
let ope_symbols = [ '=' '<' '>' '+' '-' '*' '&' '|' '\\' '/' '!' ]

rule token = parse
| "%RANK"                  { RANK }
| "%GRAMMAR"               { GRAMMAR }
| "%TRANSITION"            { TRANSITION }
| "%PRIORITY"              { PRIORITY }
| "\n"                     { Lexing.new_line lexbuf; token lexbuf }
| space+                   { token lexbuf }
| newline                  { end_of_previousline := Lexing.lexeme_end lexbuf
                           ; line_no := !line_no+1
                           ; token lexbuf
                           }
| "/*"                     { comment lexbuf; token lexbuf }
| eof                      { EOF       }
(* | "\\"                     { LAMBDA } *)
| "."                      { DOT }
| "("                      { LPAREN    }
| ")"                      { RPAREN    }
| "if"                     { IF }
| "then"                   { THEN }
| "else"                   { ELSE }
| ":"                      { COLON     }
| ","                      { COMMA }
| "int"                    { TINT      }
| "unit"                   { TUNIT     }
| "->"                     { TARROW    }
(* | "let"                    { LET }
| "in"                     { IN } *)
| digit digit*             { INT (int_of_string (Lexing.lexeme lexbuf)) }
| upper alphanum*          { IDENT (Lexing.lexeme lexbuf) }
| lower alphanum*          { IDENT (Lexing.lexeme lexbuf) }
| ope_symbols ope_symbols* { match Lexing.lexeme lexbuf with
                           | "+"           -> PLUS
                           | "-"           -> MINUS
                           (* | "*"           -> STAR *)
                           (*| "/"           -> SLASH *)
                           (*| "%"           -> PERCENT*)
                           | "="           -> EQ
                           | "!="          -> NEQ
                           | "<>"          -> NEQ
                           | "<="          -> LE
                           | ">="          -> GE
                           | "<"           -> LANGRE
                           | ">"           -> RANGRE
                           | ("&&"|"/\\")  -> AND
                           | ("||"|"\\/")  -> OR
                           | s -> failwith ("unknown operater " ^ s)
                           }

and comment = parse
(* | "*)"
    { () } *)
| "*/" { () }
(* | "(*"
    { comment lexbuf;
      comment lexbuf } *)
| "/*" 
    { comment lexbuf;
      comment lexbuf }
| eof
    { failwith "unterminated comment" }
| _
    { comment lexbuf }
and skip_all = parse
| eof { () }
| _   { skip_all lexbuf }

{
  (* This part is inserted into the end of the generated file. *)
}
