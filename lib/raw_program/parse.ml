let print_location lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "file: %s, line %d, column %d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_file file =
  Core.In_channel.with_file file ~f:(fun ch ->
    let lexbuf = Lexing.from_channel ch in
    try
      Parser.program Lexer.token lexbuf
    with Parser.Error as b->
      print_string "Parse error: ";
      print_endline @@ print_location lexbuf;
      raise b
  )