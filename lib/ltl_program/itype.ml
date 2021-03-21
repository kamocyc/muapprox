type state = State of string
[@@deriving show]

type symbol = Symbol of string
[@@deriving show]

(* intersection type *)
type itype =
    ITState of state
  | ITFunc of iarg * itype
[@@deriving show]
(* intersection type argument *)
and iarg =
    IAInt
  | IAInter of (itype * int) list (* (theta_i, m_i) < (theta_j, m_j) for each i < j *)
[@@deriving show]

type itype_env =(unit Hflmc2_syntax.Id.t * (itype * int)) list
[@@deriving show]

(* type of intersection type environment *)
type itenv_type = ITEInt | ITEInter of itype * int * int
[@@deriving show]

type itenv_item = (unit Hflmc2_syntax.Id.t) * itenv_type
[@@deriving show]

type itenv = itenv_item list
[@@deriving show]

type itype' =
    ITState' of state
  | ITFunc' of iarg * itype'
  | ITInt'
[@@deriving show]

type transition_rule = (state * symbol) * state

type priority_rule = state * int

type automaton = itype_env option * (state * transition_rule list) * priority_rule list

let show_state (State s) = s
let show_symbol (Symbol s) = s
let rec show_itype itype = match itype with
  | ITState s -> show_state s
  | ITFunc (arg, ty) -> show_iarg arg ^ "->" ^ show_itype ty
and show_iarg arg = match arg with
  | IAInt -> "int"
  | IAInter tys -> tys |> List.map (fun (ty, m) -> "(" ^ show_itype ty ^ "," ^ string_of_int m ^ ")") |> String.concat "/\\"

let show_itype_env (ienv : itype_env) =
  "[\n" ^
    (List.map (fun (id, (itype, m)) -> Hflmc2_syntax.Id.to_string id ^ ": (" ^ show_itype itype ^ ", " ^ string_of_int m ^ ")") ienv
    |> String.concat ";\n") ^
  "\n]"

let show_transition_rule ((state, symbol), target) =
  "(" ^ show_state state ^ ", " ^ show_symbol symbol ^ ") -> " ^ show_state target
  
let mk_transition_rule a b c = ((State a, Symbol b), State c)

let mk_transition_rules rules =
  match rules with
  | [] -> failwith "mk_transition_rules: no transition rule"
  | ((s, _), _)::_ -> s, rules

let show_priority_rule (state, priority) =
  show_state state ^ " -> " ^ string_of_int priority
  
let mk_priority_rule a b = (State a, b)

let eq_iarg (a: iarg) b = a = b
let eq_itype (a: itype) b = a = b
let eq_itype' (a: itype') b = a = b