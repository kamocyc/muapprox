open Itype
open Common_type

type program =
    PUnit
  | PVar of id
  | PIf of program_predicate * program * program
  | PEvent of program_event * program
  | PNonDet of program * program
  | PApp of program * program
  | PAppInt of program * arith_expr
  (* | PAbs of id * program *)
[@@deriving eq,ord,show]
and arith_expr =
    AVar of id
  | AInt of int
  | AOp of arith_op * arith_expr list
[@@deriving eq,ord,show]
and program_predicate =
  | Pred of pred_op * arith_expr list 
  | And of program_predicate * program_predicate
  | Or of program_predicate * program_predicate
  | Bool of bool
[@@deriving eq,ord,show]

let show_program p =
  let rec go_program p = match p with
    | PUnit -> "()"
    | PVar s -> s
    | PIf (p, p1, p2) -> "if " ^ go_predicate p ^ " then (" ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PEvent (pe, p) -> "event " ^ pe ^ "; " ^ go_program p
    | PNonDet (p1, p2) -> "if * then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> v
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ Arith.show_op op ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ Formula.show_pred op ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " && " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " || " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program p

let replace_var_name s =
  let pairs = [
    ("{", "");
    ("}", "");
    ("(", "_");
    (")", "_");
    (",", "_");
    ("/\\", "__and__");
    ("->", "__arw__");
  ] in
  List.fold_left (fun a (f, t) -> Str.global_replace (Str.regexp (Str.quote f)) t a) s pairs
  
let show_program_as_ocaml p =
  let rec go_program p = match p with
    | PUnit -> "()"
    | PVar s -> replace_var_name s
    | PIf (p, p1, p2) -> "if " ^ go_predicate p ^ " then (" ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PEvent (pe, p) -> "event \"" ^ pe ^ "\"; " ^ go_program p
    | PNonDet (p1, p2) -> "if read_int () then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> replace_var_name v
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ Arith.show_op op ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ Formula.show_pred op ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " && " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " || " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program p
  
type func = {
  var: id;
  args: (string * Type.simple_argty) list;
  body: program
}
[@@deriving eq,ord,show]

type hes = program * func list
[@@deriving eq,ord,show]

let show_hes ((entry, hes) : hes) = 
  "let () = " ^ show_program entry ^ "\n" ^
  (List.map (fun {var; args; body} -> "let " ^ var ^ " " ^ (String.concat " " (List.map (fun (s, t) -> "(" ^ s ^ ": " ^ Type.show_simple_argty t ^ ")") args)) ^ " = " ^ show_program body) hes |>
  String.concat "\n")
  

let show_hes_as_ocaml ((entry, hes) : hes) = 
  "let read_int () = read_int () != 0\n" ^
  "let event a = print_string a\n" ^
  (List.mapi (fun i {var; args; body} -> (if i = 0 then "let " else "and ") ^ (replace_var_name var) ^ " " ^ (String.concat " " (List.map (fun (s, t) -> "(" ^ replace_var_name s ^ ": " ^ Type.show_simple_argty t ^ ")") args)) ^ " = " ^ show_program_as_ocaml body) hes |>
  String.concat "\n") ^ "\n" ^
  "let () = " ^ show_program_as_ocaml entry
  
let convert (raw : Raw_program.raw_program) : program =
  let rec go_prog (raw : Raw_program.raw_program) : program = match raw with
    | PUnit -> PUnit
    | PVar id -> PVar id
    | PIf (p, p1, p2) -> PIf (go_pred p, go_prog p1, go_prog p2)
    | PEvent (pe, p) -> PEvent (pe, go_prog p)
    | PNonDet (p1, p2) -> PNonDet (go_prog p1, go_prog p2)
    | PApp (p1, p2) -> begin
      let p1 = go_prog p1 in
      try
        PApp (p1, go_prog p2)
      with _ -> PAppInt (p1, go_arith p2)
    end
    | _ -> failwith "go_prog"
  and go_pred (raw : Raw_program.raw_program) : program_predicate = match raw with
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
    | And (p1, p2) -> And (go_pred p1, go_pred p2)
    | Or (p1, p2) -> Or (go_pred p1, go_pred p2)
    | Bool b -> Bool b
    | _ -> failwith "go_pred"
  and go_arith (raw : Raw_program.raw_program) : arith_expr = match raw with
    | AOp (op, ps) -> AOp (op, List.map go_arith ps)
    | AInt i -> AInt i
    | PVar v -> AVar v
    | _ -> failwith "go_arith"
  in
  go_prog raw

let convert_all (raw : Raw_program.hes) =
  match 
    List.map (fun ({Raw_program.var; args; body}) -> {var; args; body = convert body}) raw |>
    List.partition (fun {var;_} -> var = "")
      with
  | [entry], xs -> entry.body, xs
  | _ -> failwith "convert_all"

(* type program' =
    PUnit'
  | PVar' of id
  | PInt' of int
  | POp' of program_op * program' * program'
  | PIf' of program_predicate * program' list * program' * program'
  | PEvent' of program_event * program'
  | PNonDet' of program' * program'
  | PApp' of program' * program'
  | PAbs' of id * program' *)

(* type typed_program = 
    PUnit of itype
  | PVar of id * itype
  | PInt of int * itype
  | POp of program_op * typed_program * typed_program * itype
  | PIf of program_predicate * typed_program list * typed_program * typed_program * itype
  | PEvent of program_event * typed_program * itype
  | PNonDet of typed_program * typed_program * itype
  | PApp of typed_program * typed_program * itype
  | PAbs of id * typed_program * itype *)

let to_uident v =
  let c = String.get v 0 in
  (Char.uppercase_ascii c |> String.make 1) ^ String.sub v 1 (String.length v - 1)
  
let replace_var_name v func_names =
  match List.find_opt ((=)v) func_names with
  | None -> replace_var_name v
  | Some _ -> replace_var_name v |> to_uident
  
let to_hflz_from_function program func_names = 
  let rec go_program program = match program with
    | PUnit -> "true"
    | PVar v -> replace_var_name v func_names
    | PIf (p, p1, p2) -> "((" ^ go_predicate p ^ " => " ^ go_program p1 ^ ") /\\ (" ^ go_predicate p ^ " => " ^ go_program p2 ^ "))"
    | PEvent (_, p) -> go_program p
    | PNonDet (p1, p2) -> "(" ^ go_program p1 ^ " /\\ " ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> replace_var_name v func_names
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ " " ^ Arith.show_op op ^ " " ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "to_hflz: go_arith"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ " " ^ Formula.show_pred op ^ " " ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "to_hflz: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " /\\ " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " \\/ " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program program

let to_hflz hes priority =
  let entry, hes = hes in
  if List.length hes <> List.length priority then failwith "to_hflz";
  let func_names = List.map (fun {var;_} -> var) hes in
  let hes = List.map (fun ({var; _} as p) ->
    match List.assoc_opt var priority with
    | None -> failwith "to_hflz (2)"
    | Some pr -> (pr, p)) hes in
  let hes = List.sort (fun (pr, _) (pr', _) -> compare pr pr') hes |> List.rev in
  "%HES\n" ^
  "Sentry =v " ^ to_hflz_from_function entry func_names ^ ".\n" ^
  (List.map (fun (pr, {var; args; body}) ->
    replace_var_name var func_names ^ " " ^ (String.concat " " (List.map (fun (a, _) -> replace_var_name a func_names) args)) ^ " =" ^
      (if pr mod 2 = 0 then "v" else "u") ^ " " ^ to_hflz_from_function body func_names ^ "."
  ) hes |>
  String.concat "\n")
  