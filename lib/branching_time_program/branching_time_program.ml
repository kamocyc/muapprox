
let verifyParseResult (ranks, gram, (aut, prs)) =
  let grammar = To_horsz.to_horsz ranks gram in
  let automata = AlternatingAutomaton.from_transitions (ranks,aut,prs) in
  Horsz.print grammar;
  AlternatingAutomaton.print automata;
  let hes = To_hflz.trans_horsz automata grammar in
  ignore @@ Manipulate.Print_syntax.MachineReadable.save_hes_to_file ~file:"aaa.txt" ~without_id:true true hes;
  ()
  
let branching_time_program file =
  (* let file = "/opt/home2/git/muapprox/benchmark/prog2/ata.txt" in *)
  let parseresult = Parse.parse_file file in
  verifyParseResult parseresult