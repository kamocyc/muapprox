module Alternating_automaton = Alternating_automaton
module Trans_program = Trans_program
module Horsz = Horsz
module To_hflz = To_hflz

let parse_file_horsz file =
  let buf = Hflmc2_util.read_file file in
  let line_number = Hflmc2_util.count_substring buf "\n" in
  Hflmc2_util.Parse.parse_file Lexer.token Parser.main [(1, line_number + 1)] file

let translate_branching_time_program_horsz file =
  let (ranks_gram, (aut, prs)) = parse_file_horsz file in
  match ranks_gram with
  | None -> failwith "input file should contain terminals' rank and grammar"
  | Some (ranks, gram) -> begin
    (* read HORSz *)
    let grammar = To_horsz.to_horsz ranks gram in
    let automata = Alternating_automaton.from_transitions (ranks, aut, prs) in
    Horsz.print grammar true;
    Alternating_automaton.print automata;
    let hes = To_hflz.trans_horsz automata grammar in
    hes
  end

let translate_branching_time_program file =
  let get_random_file_name () = Printf.sprintf "/tmp/%d.tmp" (Random.self_init (); Random.int 0x10000000) in
  let extracted, extracted_line_numbers, remaining, remaining_line_numbers = Raw_program.Program_main.split_with file "%PROGRAM" in
  let extracted_file = get_random_file_name () in
  let remaining_file = get_random_file_name () in
  Hflmc2_util.write_file extracted_file extracted;
  Hflmc2_util.write_file remaining_file remaining;
  print_endline "parse_file";
  print_endline @@ extracted_file;
  print_endline @@ remaining_file;
  let program = Raw_program.Program_main.parse_file extracted_line_numbers extracted_file in
  let (ranks_gram, (aut, prs)) = Hflmc2_util.Parse.parse_file Lexer.token Parser.main remaining_line_numbers remaining_file in
  match ranks_gram with
  | Some _ -> failwith "input file should NOT contain terminals' rank and grammar"
  | None -> begin
    let program' = Raw_program.Trans_raw_program.convert_all program in
    let () =
      print_endline "program:"; print_endline @@ Raw_program.Print_syntax.show_program program'; print_endline ""
    in
    let (grammar, ranks) = Trans_program.trans program' in
    let automata = Alternating_automaton.from_transitions (ranks, aut, prs) in
    Horsz.print grammar true;
    Alternating_automaton.print automata;
    let hes = To_hflz.trans_horsz automata grammar in
    hes
  end
  
let branching_time_program is_input_horsz file =
  if is_input_horsz then
    translate_branching_time_program_horsz file
  else
    translate_branching_time_program file
  
