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

let check_branching_events (program : Raw_program.Program.program_expr * Raw_program.Program.program_function list) (aut : ((string * string) * Raw_horsz.preformula) list) =
  let get_branching_events (entry, functions) =
    let combine ds =
      List.fold_left (fun (acc1, acc2) (d1, d2) -> (acc1 @ d1, acc2 @ d2)) ([], []) ds
    in
    let rec go expr = match expr with
      | Raw_program.Program.PUnit | PVar _ -> ([], [])
      | PNonDet (e1, e2, _, e) -> begin
        let e =
          match e with
          | Some e -> e
          | None -> failwith "check_branching_events: non-deterministic choice needs event name"
        in
        combine [(go e1); (go e2); ([e], [])]
      end
      | PIf (p, e1, e2) ->
        combine [(go_pred p); (go e1); (go e2)]
      | PEvent (_, e1) ->
        go e1
      | PApp (e1, e2) ->
        combine [go e1; go e2]
      | PAppInt (e1, a1) ->
        combine [go e1; go_arith a1]
    and go_pred p = match p with
      | Pred (_, a) -> combine (List.map go_arith a)
      | And (p1, p2) -> combine [go_pred p1; go_pred p2]
      | Or (p1, p2) -> combine [go_pred p1; go_pred p2]
      | Bool _ -> ([], [])
    and go_arith a = match a with
      | AVar _ | AInt _ -> ([], [])
      | AOp (_, a) -> combine (List.map go_arith a)
      | ANonDet (_, e) -> begin
        let e =
          match e with
          | Some e -> e
          | None -> failwith "check_branching_events: non-deterministic integer should have an event name"
        in
        ([], [e])
      end
    in
    combine (go entry :: (List.map (fun {Raw_program.Program.body; _} -> go body) functions))
  in
  let states = Alternating_automaton.states_in_transitions aut in
  let check_transitions nondet_events formula_checker =
    List.iter
      (fun e ->
        List.iter
          (fun q ->
            match List.find_all (fun ((q', e'), _) -> q = q' && e = e') aut with
            | [(_, fml)] -> begin
              try
                formula_checker fml (q, e)
              with Assert_failure _ ->
                failwith @@ "(" ^ q ^ ", " ^ e ^ ", " ^ Raw_horsz.string_of_ata_formula fml ^ ")"
            end
            | [] -> failwith @@ "transition not found (" ^ q ^ ", " ^ e ^ ")"
            | _ -> failwith @@ "multiple transition found (" ^ q ^ ", " ^ e ^ ")"
          )
          states
      )
      nondet_events
  in
  let (p_nondets, a_nondets) = get_branching_events program in
  let a_nondets = List.filter (fun e -> e <> Trans_program.a_non_det_forall && e <> Trans_program.a_non_det_exists) a_nondets in
  check_transitions
    p_nondets
    (fun fml (_, _) -> match fml with
      | FAnd (FVar (i1, q1), FVar (i2, q2)) ->
        assert (i1 = 1 && i2 == 2);
        ()
      | FOr (FVar (i1, q1), FVar (i2, q2)) ->
        assert (i1 = 1 && i2 == 2);
        ()
      | FConst "false" -> ()
      | _ -> assert false
    );
  check_transitions
    a_nondets
    (fun fml (_, _) -> match fml with
      | FAnd (FVar (i1, q1), FAnd (FVar (i2, q2), FVar (i3, q3))) ->
        assert (i1 = 1 && i2 == 2 && i3 == 3);
        assert (q2 = q3);
        assert (q1 <> q2);
        ()
      | FOr (FVar (i1, q1), FOr (FVar (i2, q2), FVar (i3, q3))) ->
        assert (i1 = 1 && i2 == 2 && i3 == 3);
        assert (q2 = q3);
        assert (q1 <> q2);
        ()
      | FConst "false" -> ()
      | _ -> assert false
    )
  
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
    check_branching_events program' aut;
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
  
