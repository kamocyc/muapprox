open Raw_program
open Itype

let id x = x

let check_input (program : Raw_program.Program.program) (automaton : automaton) =
  let (env, (State initial_state, trans), priority) = automaton in
  (* TODO: check environment? *)
  
  let all_symbols = Program.get_events program in
  
  let all_states = List.map (fun ((State s, _), _) -> s) trans |> List.sort_uniq compare in
  
  if not @@ List.exists ((=) initial_state) all_states then
    failwith @@ "initial_state " ^ initial_state ^ " does not exist in the transition rules";
  
  let grouped_trans =
    let ht = Hflmc2_util.group_by (fun ((State a, _), _) -> a) trans in
    Hashtbl.fold (fun k v acc -> (k, List.map (fun ((_, Symbol a), _) -> a) v)::acc) ht [] in
  
  List.iter (fun (state, targets) ->
    let targets = List.sort_uniq compare targets in
    if all_symbols <> targets then
      failwith @@ "some transition states are missing (state=" ^ state ^ ", all_symbols=" ^ Hflmc2_util.show_list id all_symbols ^ " / targets=" ^ Hflmc2_util.show_list id targets ^ ")"
  ) grouped_trans;
  
  if (List.map (fun (State s, _) -> s) priority |> List.sort compare) <> all_states then
    failwith @@ "priority rules are not matched (all_states=" ^ Hflmc2_util.show_list id all_states ^ " / priority=" ^ (Hflmc2_util.show_list id (List.map (fun (State s, _) -> s) priority)) ^ ")"
  

