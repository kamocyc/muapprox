let typing hes =
  hes (* TODO *)

let get_position_string (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d"
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_from_lexbuf lexbuf =
  try
    let hes =
      lexbuf
      |> HesParsing.toplevel HesLexer.main
      |> typing
    in
    Ok hes
  with
  | HesParsing.Error ->
    Error (Printf.sprintf "%s: syntax error" (get_position_string lexbuf))
  | HesLexer.SyntaxError error ->
    Error (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let from_file file =
  let ic = open_in file in
  Lexing.from_channel ic
  |> parse_from_lexbuf

let parse str =
  Lexing.from_string str
  |> parse_from_lexbuf
