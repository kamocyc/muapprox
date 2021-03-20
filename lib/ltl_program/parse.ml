let translate_line_number original_line_numbers line_org =
  let line = ref line_org in
  let result = ref None in
  List.iter (fun (froml, tol) ->
    match !result with
    | None -> begin
      line := !line - (tol - froml + 1);
      if !line <= 0 then begin
        if tol + !line < froml then failwith @@ "translate_line_number: illegal line number (too small): " ^ string_of_int line_org;
        result := Some (tol + !line)
      end
    end
    | Some _ -> ()
  ) original_line_numbers;
  match !result with
  | Some l -> l
  | None -> failwith @@ "translate_line_number: illegal line number (too large): " ^ string_of_int line_org

let print_location original_line_numbers lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "file: %s, line %d, column %d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_file file =
  Core.In_channel.with_file file ~f:(fun ch ->
    let lexbuf = Lexing.from_channel ch in
    try
      Parser.main Lexer.token lexbuf
    with Parser.Error as b->
      print_string "Parse error: ";
      print_endline @@ print_location [] lexbuf;
      raise b
  )