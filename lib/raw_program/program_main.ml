open Program

module Print_syntax = Print_syntax

let convert_ltl file =
  let program = Parse.parse_file file in
  
  print_endline @@ Program_raw.show_raw_program program;
  
  let program' = Trans_raw_program.convert_all program in
  let () =
    print_endline "program:"; print_endline @@ Print_syntax.show_program program'; print_endline ""
  in
  program'
