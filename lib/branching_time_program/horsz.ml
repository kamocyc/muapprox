open Hflmc2_syntax

type terminal = string
[@@deriving eq,ord,show]

let show_terminal x = x

type nonterminal = string * int
[@@deriving eq,ord,show]

type op = Arith.op
[@@deriving eq,ord,show]

let show_op p = match p with 
  | Arith.Add -> "+"
  | Arith.Sub -> "-"
  | Arith.Mult -> "*"
  | Arith.Div -> "/"
  | Arith.Mod -> "%"
  
type 'var gen_arith =
  | Int of int
  | AVar of 'var
  | Op  of op * 'var gen_arith list
  [@@deriving eq,ord,show]

type arith = [`Int] Id.t gen_arith
  [@@deriving eq,ord,show]

type pred = Formula.pred
[@@deriving eq,ord,show]

let pred s = match s with
  | Formula.Eq  -> "="
  | Formula.Neq -> "!="
  | Formula.Le  -> "<="
  | Formula.Ge  -> ">="
  | Formula.Lt  -> "<"
  | Formula.Gt  -> ">"
    
(* formula parametrized by variable type and arith type *)
type formula =
  | Bool of bool
  | Or   of formula * formula
  | And  of formula * formula
  | Pred of pred * arith list
  [@@deriving eq,ord,show]

type 'ty horsz_expr =
  | PVar of 'ty Id.t
  | App of 'ty horsz_expr * 'ty horsz_expr
  | AppInt of 'ty horsz_expr * arith
  | If of formula * 'ty horsz_expr * 'ty horsz_expr
  | Terminal of terminal * 'ty horsz_expr list
  [@@deriving eq,ord,show]

type horsz_expr_s = Type.simple_ty horsz_expr
[@@deriving eq,ord,show]
  
type 'ty horsz_rule = {var: 'ty Id.t; args: 'ty Type.arg Id.t list; body: 'ty horsz_expr}
[@@deriving eq,ord,show]

type 'ty horsz = ('ty horsz_expr * 'ty horsz_rule list)
[@@deriving eq,ord,show]

let show_arith a =
  let rec go a = match a with
    | Int i -> string_of_int i
    | AVar s -> Id.to_string ~without_id:false s
    | Op (op, [a1; a2]) -> 
      "(" ^ go a1 ^ " " ^ show_op op ^ " " ^ go a2 ^ ")"
    | Op _ -> assert false
  in
  go a
  
let show_formula a =
  let rec go a = match a with
    | Bool b -> string_of_bool b
    | Or (p1, p2) -> "(" ^ go p1 ^ " \\/ " ^ go p2 ^ ")"
    | And (p1, p2) -> "(" ^ go p1 ^ " /\\ " ^ go p2 ^ ")"
    | Pred (p, [p1; p2]) -> "(" ^ show_arith p1 ^ " " ^ pred p ^ " " ^ show_arith p2 ^ ")"
    | Pred _ -> assert false
    in
  go a

let show_horsz_expr expr = 
  let rec go expr = match expr with
    | PVar v -> Id.to_string ~without_id:false v
    | App (p1, p2) -> "(" ^ go p1 ^ " " ^ go p2 ^ ")"
    | AppInt (p1, a) -> "(" ^ go p1 ^ " " ^ show_arith a ^ ")"
    | If (c, p1, p2) -> "(if " ^ show_formula c ^ " then " ^ go p1 ^ " else " ^ go p2
    | Terminal (t, ps) -> "(" ^ show_terminal t ^ " " ^ ((List.map (fun p -> go p) ps) |> String.concat " ") ^ ")"
  in
  go expr

let show_horsz (g : Type.simple_ty horsz) =
  let (entry, rules) = g in
  "S -> " ^ show_horsz_expr entry ^ ".\n" ^
  (List.map (fun {var; args; body} ->
    Id.to_string ~without_id:true var ^ " " ^
    ((List.map (fun id -> Id.to_string ~without_id:true id) args) |> String.concat " ") ^
    " -> " ^ show_horsz_expr body ^ ".\n"
  ) rules
  |> String.concat "")
  
let print (g : Type.simple_ty horsz) = print_endline @@ show_horsz g
