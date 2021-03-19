  
let branching_time_program file =
  let (ranks, gram, (aut, prs)) = Parse.parse_file file in
  let grammar = To_horsz.to_horsz ranks gram in
  let automata = AlternatingAutomaton.from_transitions (ranks,aut,prs) in
  Horsz.print grammar;
  AlternatingAutomaton.print automata;
  let hes = To_hflz.trans_horsz automata grammar in
  hes
