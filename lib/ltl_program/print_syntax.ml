open Hflmc2_syntax
open Itype
open Common_type
open Program

let show_pred (op : Formula.pred) = match op with
  | Formula.Eq  -> "="
  | Formula.Neq -> "<>"
  | Formula.Le  -> "<="
  | Formula.Ge  -> ">="
  | Formula.Lt  -> "<"
  | Formula.Gt  -> ">"

let show_op (op : Arith.op) = match op with
  | Arith.Add -> "+"
  | Arith.Sub -> "-"
  | Arith.Mult -> "*"
  | Arith.Div -> "/"
  | Arith.Mod -> "mod"

let rec show_simple_ty (ty : Type.simple_ty) = match ty with
  | TyBool _ -> "bool"
  | TyArrow (a, b) -> "(" ^ show_simple_argty a.ty ^ " -> " ^ show_simple_ty b ^ ")"
and show_simple_argty (ty : Type.simple_argty) = match ty with
  | TyInt -> "int"
  | TySigma ty -> show_simple_ty ty
   
let show_program p =
  let rec go_program p = match p with
    | PUnit -> "()"
    | PVar s -> Id.to_string ~without_id:true s
    | PIf (p, p1, p2) -> "if " ^ go_predicate p ^ " then (" ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PEvent (pe, p) -> "event " ^ pe ^ "; " ^ go_program p
    | PNonDet (p1, p2, _) -> "if * then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> (Id.to_string ~without_id:true v)
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ " " ^ show_op op ^ " " ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
    | ANonDet _ -> "*"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ " " ^ show_pred op ^ " " ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " && " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " || " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program p

let show_raw_id_name = ref false

let replace_var_name s =
  let pairs =
    (if !show_raw_id_name then []
    else [
      ("{", "");
      ("}", "");
      ("(", "_");
      (")", "_");
      (",", "_");
      ("/\\", "__and__");
      ("->", "__arw__");
    ]) in
  List.fold_left (fun a (f, t) -> Str.global_replace (Str.regexp (Str.quote f)) t a) s pairs
  
let show_program_as_ocaml p =
  let rec go_program p = match p with
    | PUnit -> "()"
    | PVar s -> begin
      let name = replace_var_name (Id.to_string ~without_id:true s) in
      match s.ty with
      | Type.TyBool _ -> "(" ^ name ^ " ())"
      | Type.TyArrow _ -> name
    end
    | PIf (p, p1, p2) -> "if " ^ go_predicate p ^ " then (" ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PEvent (pe, p) -> "event \"" ^ pe ^ "\"; " ^ go_program p
    | PNonDet (p1, p2, _) -> "if read_bool () then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> replace_var_name (Id.to_string ~without_id:true v)
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ show_op op ^ go_arith arg2 ^ ")"
    | ANonDet _ -> "(read_int ())"
    | AOp _ -> failwith "show_program: go_arith"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ show_pred op ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " && " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " || " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program p

let show_program ((entry, funcs) : program) = 
  "let () = " ^ show_program entry ^ "\n" ^
  (
    List.map (fun {var; args; body} ->
      "let " ^ Id.to_string ~without_id:true var ^ " " ^
        (String.concat " " (List.map (fun {Id.name; ty} -> "(" ^ name ^ ": " ^ show_simple_argty ty ^ ")") args)) ^
        " = " ^ show_program body
    ) funcs |>
    String.concat "\n"
  )

let show_program_as_ocaml ((entry, funcs) : program) = 
  "let read_bool () = read_int () != 0\n" ^
  "let event a = print_string a\n" ^
  (List.mapi (
    fun i {var; args; body} ->
      (if i = 0 then "let rec " else "and ") ^
      (replace_var_name (Id.to_string var ~without_id:true)) ^ " " ^
      (if List.length args = 0 then "() " else "") ^
      (String.concat " " (List.map (fun {Id.name; ty} -> "(" ^ replace_var_name name ^ ": " ^ show_simple_argty ty ^ ")") args)) ^ " = " ^
      show_program_as_ocaml body) funcs |>
  String.concat "\n") ^ "\n" ^
  "let _ = " ^ show_program_as_ocaml entry
  