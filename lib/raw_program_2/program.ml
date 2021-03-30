open Hflmc2_syntax
open Common_type

type program_expr =
    PUnit
  | PVar of Type.simple_ty id
  | PIf of program_predicate * program_expr * program_expr
  | PEvent of program_event * program_expr
  | PNonDet of program_expr * program_expr * int option * program_event option
  | PApp of program_expr * program_expr
  | PAppInt of program_expr * arith_expr
  (* | PAbs of id * program_expr *)
[@@deriving eq,ord,show]
and arith_expr =
    AVar of [`Int] id
  | AInt of int
  | AOp of arith_op * arith_expr list
  | ANonDet of int option * program_event option (* id for translation*)
[@@deriving eq,ord,show]
and program_predicate =
  | Pred of pred_op * arith_expr list 
  | And of program_predicate * program_predicate
  | Or of program_predicate * program_predicate
  | Bool of bool
[@@deriving eq,ord,show]
  
type program_function = {
  var: Type.simple_ty id;
  args: Type.simple_argty id list;
  body: program_expr
}
[@@deriving eq,ord,show]

type program = program_expr * program_function list
[@@deriving eq,ord,show]

let get_events (program : program) =
  let rec go (program : program_expr) = match program with
    | PUnit -> []
    | PVar _ -> []
    | PIf (p, p1, p2) -> (go_pred p) @ go (p1) @ go (p2)
    | PEvent (e, p) -> e :: (go p)
    | PNonDet (p1, p2, _, e) ->
      (match e with
      | Some e -> [e]
      | None -> []) @
      go (p1) @ go (p2)
    | PApp (p1, p2) -> go p1 @ go p2
    | PAppInt (p1, a) -> go p1 @ go_arith a
  and go_pred p = match p with
    | Pred (_, es) -> List.map go_arith es |> List.flatten
    | Or (p1, p2) -> go_pred p1 @ go_pred p2
    | And (p1, p2) -> go_pred p1 @ go_pred p2
    | Bool _ -> []
  and go_arith arith = match arith with
    | AVar _ -> []
    | AInt _ -> []
    | AOp (_, es) -> List.map go_arith es |> List.flatten
    | ANonDet (_, e) -> (match e with Some e -> [e] | None -> [])
  in
  let entry, rules = program in
  ((go entry) @
  (List.map (fun {body} -> go body) rules |> List.flatten))
  |> List.sort_uniq compare
