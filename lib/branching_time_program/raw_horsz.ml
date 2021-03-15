open Hflmc2_syntax

type 'a raw_expression_gen =
  | PVar of 'a
  | PIf of 'a raw_expression_gen * 'a raw_expression_gen * 'a raw_expression_gen
  | PApp of 'a raw_expression_gen * 'a raw_expression_gen
  | AInt of int
  | AOp of Arith.op * 'a raw_expression_gen list
  | Pred of Formula.pred * 'a raw_expression_gen list 
  | And of 'a raw_expression_gen * 'a raw_expression_gen
  | Or of 'a raw_expression_gen * 'a raw_expression_gen
  [@@deriving eq,ord,show]

type raw_expression = (string * Type.simple_argty option) raw_expression_gen
[@@deriving eq,ord,show]

type 'a raw_function_gen = {
  var: 'a;
  args: 'a list;
  body: 'a raw_expression_gen
}
[@@deriving eq,ord,show]

type raw_function = (string * Type.simple_argty option) raw_function_gen
[@@deriving eq,ord,show]

type 'a raw_program_gen = 'a raw_function_gen list
[@@deriving eq,ord,show]

type raw_program = (string * Type.simple_argty option) raw_program_gen
[@@deriving eq,ord,show]

let mk_int n  = AInt n
let mk_var x     = PVar (x, None)
let mk_op op as' = AOp(op, as')

let mk_ands = function
  | [] -> failwith "mk_ands"
  | x::xs -> Core.List.fold_left xs ~init:x ~f:(fun a b -> And(a, b))

let mk_ors = function
  | [] -> failwith "mk_ors"
  | x::xs -> Core.List.fold_left xs ~init:x ~f:(fun a b -> Or(a, b))

(* let mk_not x = Not x *)

let mk_arg s t = (s, t)

let mk_pred pred a1 a2 = Pred(pred, [a1;a2])

let mk_app t1 t2 = PApp(t1, t2)
let mk_apps t ts = Core.List.fold_left ts ~init:t ~f:mk_app
let mk_if p t e = PIf (p, t, e)


(* automaton *)
type preformula = FConst of string 
                | FVar of int * string 
                | FAnd of preformula * preformula
                | FOr of preformula * preformula
type ata_trans = (string * string) * preformula
type ata_priority = string * int
type automaton = (ata_trans list) * (ata_priority list)

let mk_input (ranks, gram, (aut, pri)) =
  (gram, (ranks, aut, pri))

let rec string_of_states qs =
  match qs with
    [] -> ""
  | q::qs' -> q^" "^(string_of_states qs')

let string_of_transition ((q,a), qs) =
  q^" "^a^" -> "^(string_of_states qs)

let rec string_of_transitions_aux trs =
  match trs with
   [] -> ""
 | tr::trs' ->
     (string_of_transition tr)^".\n"^(string_of_transitions_aux trs')
let string_of_transitions trs = 
  "%BEGINA\n"^(string_of_transitions_aux trs)^"%ENDA\n";;

let rec string_of_ata_formula = function
  | FConst s -> s
  | FVar (i,q) -> "(" ^ string_of_int i ^ "," ^ q ^ ")"
  | FAnd (f1,f2) -> "(" ^ string_of_ata_formula f1 ^ " /\\ " 
                      ^ string_of_ata_formula f2 ^ ")"
  | FOr (f1,f2) -> "(" ^ string_of_ata_formula f1 ^ " \\/ " 
                      ^ string_of_ata_formula f2 ^ ")"


let string_of_ata_rule ((q,a), fml ) =
  q ^ " " ^ a ^ " -> " ^ (string_of_ata_formula fml)

let rec string_of_ata_rules_aux trs =
  match trs with
    [] -> ""
 |  tr :: trs ->
     (string_of_ata_rule tr) ^ ".\n" ^ (string_of_ata_rules_aux trs)

let string_of_priority (q,p) =
  q ^ " -> " ^ string_of_int p
  
let rec string_of_priorities_aux prs =
  match prs with
    [] -> ""
  | pr::prs ->
    (string_of_priority pr) ^ ".\n" ^ (string_of_priorities_aux prs)
    
let string_of_automaton (rs, trs, prs) =
  "%BEGINR\n"^
    String.concat "" (List.map (fun (q,i) -> q ^" -> "^string_of_int i^".\n") rs) ^
  "%ENDR\n"^
  "%BEGINATA\n"^(string_of_ata_rules_aux trs)^"%ENDATA\n" ^
  "%BEGINP\n"^(string_of_priorities_aux prs)^"%ENDP\n"    
