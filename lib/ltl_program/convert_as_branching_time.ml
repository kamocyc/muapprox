open Branching_time_program
(* TODO: integerに未対応 *)

let nondet_demonic_event = "demonic_non_determinism"
let nondet_integer_demonic_event = "demonic_integer_non_determinism"

let assign_event_in_non_determinism program =
  let open Raw_program.Program in
  (* assign events to non-determinism *)
  let rec go_expr expr = match expr with
    | PUnit | PVar _ -> expr
    | PIf (p, e1, e2) -> PIf (go_pred p, go_expr e1, go_expr e2)
    | PEvent (e, e1) -> PEvent (e, go_expr e1)
    | PNonDet (e1, e2, m, _) -> PNonDet (go_expr e1, go_expr e2, m, Some nondet_demonic_event)
    | PApp (e1, e2) -> PApp (go_expr e1, go_expr e2)
    | PAppInt (e1, a1) -> PAppInt (go_expr e1, go_arith a1)
  and go_arith arith = match arith with
    | AVar _ | AInt _ -> arith
    | AOp (op, xs) -> AOp (op, List.map go_arith xs)
    | ANonDet (i, _) -> ANonDet (i, Some nondet_integer_demonic_event)
  and go_pred pred = match pred with
    | Pred (op, xs) -> Pred (op, List.map go_arith xs)
    | And (p1, p2) -> And (go_pred p1, go_pred p2)
    | Or (p1, p2) -> Or (go_pred p1, go_pred p2)
    | Bool _ -> pred
  in
  let (entry, rules) = program in
  go_expr entry,
  List.map
    (fun rule -> { rule with body = go_expr rule.body })
    rules

let convert
    program
    (automaton :
      ((unit Hflmc2_syntax.Id.t * (Itype.itype * int)) list option *
      (Itype.state *
        ((Itype.state * Itype.symbol) *
        Itype.state)
        list) *
      (Itype.state * int) list)) =
  let program = assign_event_in_non_determinism program in
  let (_, (State init, transition), priority) = automaton in
  let open Alternating_automaton in
  let (grammar, ranks) = Trans_program.trans program in
  let delta =
    transition 
    |> Hflmc2_util.group_by (fun (key, _) -> key)
    |> Hflmc2_util.list_of_hashtbl
    |> List.map (fun ((Itype.State state, Itype.Symbol symbol), rules) ->
      let clause = List.map (fun (_, Itype.State state') -> [CVar (1, state')]) rules in
      ((state, symbol), clause)
    )
  in
  let omega = List.map (fun (Itype.State s, i) -> (s, i)) priority in
  let st = List.map (fun (Itype.State s, _) -> s) priority in
  let delta =
    delta @
    List.map (fun state ->
      ((state, nondet_demonic_event), [[CVar (1, state); CVar (2, state)]])
    ) st @
    List.map (fun state ->
      ((state, nondet_integer_demonic_event), [[CVar (1, state); CVar (2, state); CVar (3, state)]])
    ) st in
    (* TODO: *)
  (* check_branching_events program transition; *)
  let automata = {
    alpha = ranks;
    st;
    delta;
    init;
    omega
  } in
  Horsz.print grammar true;
  Alternating_automaton.print automata;
  let hes = To_hflz.trans_horsz automata grammar in
  hes
  