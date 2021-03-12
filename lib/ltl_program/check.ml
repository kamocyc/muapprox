open Program
open Itype
open Trans_ltl

let get_events (program : program) =
  let rec go (program : program_expr) = match program with
    | PUnit -> []
    | PVar _ -> []
    | PIf (_, p1, p2) -> go (p1) @ go (p2)
    | PEvent (e, p) -> e :: (go p)
    | PNonDet (p1, p2, _) -> go (p1) @ go (p2)
    | PApp (p1, p2) -> go (p1) @ go (p2)
    | PAppInt (p1, a) -> go p1
  in
  let entry, rules = program in
  ((go entry) @
  (List.map (fun {body} -> go body) rules |> List.flatten))
  |> List.sort_uniq compare

let contains_duplicates ls = (List.length @@ List.sort_uniq compare ls) <> List.length ls

let group_by f l1 =
  List.fold_left
    (fun acc e ->
      let key = f e in
      let mem = try Hashtbl.find acc key with Not_found -> [] in
      Hashtbl.replace acc key (e::mem);
      acc
    )
    (Hashtbl.create 100)
    l1

let id x = x

let check_input (program : program) (automaton : automaton) =
  let (env, (State initial_state, trans), priority) = automaton in
  (* TODO: check environment? *)
  
  let all_symbols = get_events program in
  
  let all_states = List.map (fun ((State s, _), _) -> s) trans |> List.sort_uniq compare in
  
  if not @@ List.exists ((=) initial_state) all_states then
    failwith @@ "initial_state " ^ initial_state ^ " does not exist in the transition rules";
  
  let grouped_trans =
    let ht = group_by (fun ((State a, _), _) -> a) trans in
    Hashtbl.fold (fun k v acc -> (k, List.map (fun ((_, Symbol a), _) -> a) v)::acc) ht [] in
  
  List.iter (fun (state, targets) ->
    let targets = List.sort_uniq compare targets in
    if all_symbols <> targets then
      failwith @@ "some transition states are missing (state=" ^ state ^ ", all_symbols=" ^ Print_syntax.show_list id all_symbols ^ " / targets=" ^ Print_syntax.show_list id targets ^ ")"
  ) grouped_trans;
  
  if (List.map (fun (State s, _) -> s) priority |> List.sort compare) <> all_states then
    failwith @@ "priority rules are not matched (all_states=" ^ Print_syntax.show_list id all_states ^ " / priority=" ^ (Print_syntax.show_list id (List.map (fun (State s, _) -> s) priority)) ^ ")"
  

