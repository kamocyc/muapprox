open Common_type

(* intersection type *)
type itype =
    ITState of string
  | ITFunc of iarg * itype
[@@deriving show]
(* intersection type argument *)
and iarg =
    IAInt
  | IAInter of (itype * int) list (* (theta_i, m_i) < (theta_j, m_j) for each i < j *)
[@@deriving show]

type itype_env =(string * (itype * int)) list
[@@deriving show]

let rec show_itype itype = match itype with
  | ITState s -> s
  | ITFunc (arg, ty) -> show_iarg arg ^ "->" ^ show_itype ty
and show_iarg arg = match arg with
  | IAInt -> "int"
  | IAInter tys -> tys |> List.map (fun (ty, m) -> "(" ^ show_itype ty ^ "," ^ string_of_int m ^ ")") |> String.concat "/\\"
  
(* type of intersection type environment *)
type itenv_type = ITEInt | ITEInter of itype * int * int

type itenv_item = id * itenv_type
type itenv = itenv_item list

type transition_rule = (string * string) * string
let show_transition_rule ((state, symbol), target) =
  "(" ^ state ^ ", " ^ symbol ^ ") -> " ^ target
  
let mk_transition_rule a b c = ((a, b), c)

type priority_rule = string * int
let show_priority_rule (state, priority) =
  state ^ " -> " ^ string_of_int priority
  
let mk_priority_rule a b = (a, b)
