open Core
open Logic

let parse_from_file filename =
  Ok(match LPParser.parser_main_logic_program LPLexer.token (Lexing.from_channel (In_channel.create filename)) with
      | [] -> Formula.mk_atom (Atom.mk_true Dummy) Dummy
      | (x, y) :: cs ->
        List.fold_left cs
          ~init:(Formula.mk_imply x y Dummy)
          ~f:(fun acc (x, y) ->
              Formula.mk_and
                acc
                (Formula.mk_imply x y Dummy)
                Dummy
            ))



