open Util

type state = string;;
type index = int;;

type literal = CVar of index * state
type clause = literal list
type dnf = clause list

type t = { alpha : (string * int) list; 
           st    : state list; 
           delta : ((state * string) * dnf) list;
           init  : state;
           omega : (string * int) list };;

let show_dnf (dnf : dnf) =
  List.map (fun clause ->
    "(" ^
    (List.map
      (fun (CVar (i, s)) -> "(" ^ string_of_int i ^ "," ^ s ^ ")")
      clause
    |> String.concat " /\\ ") ^
    ")"
  ) dnf
  |> String.concat " \\/ "

let to_dnf (fml : Raw_horsz.preformula) =
  let distribute f1 f2 =
    list_product f1 f2
    |> List.map (fun (c1, c2) ->
      c1 @ c2
    )
  in
  let rec go fml =
    (* dnf:  (a /\ b /\ c) \/ (d \/ e \/ f) *)
    (* http://cs.jhu.edu/~jason/tutorials/convert-to-CNF *)
    match fml with
    | Raw_horsz.FVar (i, s) -> [[CVar (i, s)]]
    | FOr (f1, f2) ->
      (* f1とf2はdnf *)
      let f1 = go f1 in
      let f2 = go f2 in
      f1 @ f2
    | FAnd (f1, f2) ->
      let f1 = go f1 in
      let f2 = go f2 in
      distribute f1 f2
    | _ -> failwith "to_dnf"
  in
  go fml

let get_transition automaton state symbol =
  let { delta } = automaton in
  match List.find_all (fun ((state', symbol'), trans) -> state = state' && symbol = symbol') delta with
  | [(_, t)] -> t
  | [] -> failwith "get_transition"
  | _ -> assert false
  
let get_prioirty automaton state =
  let { omega } = automaton in
  match List.find_all (fun (s, i) -> s = state) omega with
  | [(_, x)] -> x
  | [] -> failwith "get_priority"
  | _ -> assert false

let print m =
  print_string "alpha:\n";
  print_string "{";
  List.iter (fun (a, i) -> print_string (a ^ " -> " ^ string_of_int i ^ "; ")) m.alpha;
  print_string "}";
  print_string "\n";
  print_string "states:\n";
  print_string "{";
  List.iter (fun q ->
    match List.find_all (fun (s, i) -> s = q) m.omega with
    | [(_, pr)] ->
      print_string (q ^ " -> " ^ string_of_int pr ^ "; ")
    | [] -> failwith @@ "not found priority" ^ q
    | _ -> assert false
  ) m.st;
  print_string "}\n";
  print_string "delta:\n";
  List.iter (fun ((q,a),fml) -> 
    print_string ("" ^ q ^ " " ^ a ^ " -> ");
    print_string @@ show_dnf fml;
    print_newline ()) m.delta;
  print_string ("init: " ^ m.init ^"\n");;

let states_in_preformula fml = 
  let rec go = function
    | Raw_horsz.FConst _ -> []
    | FVar (i,q) -> [q]
    | FAnd (f1,f2) | FOr (f1,f2) ->
        merge_and_unify compare (go f1) (go f2)
  in go fml;;

let states_in_tr ((q, a), fml) =
  merge_and_unify compare [q] (states_in_preformula fml);;

let states_in_transitions transitions =
  merge_and_unify_list compare (List.map states_in_tr transitions);;

let from_transitions (ranks,transitions,prs) =
  let alpha = ranks in
  let init = fst (fst (List.hd transitions)) in
  let st = states_in_transitions transitions in
  (* TODO: check *)
  let delta = List.map (fun (k, v) -> (k, to_dnf v)) transitions in
  { alpha = alpha; st = st; delta = delta; init = init; omega = prs };;
