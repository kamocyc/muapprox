open Hflmc2_syntax
open Itype
open Common_type

type program =
    PUnit
  | PVar of Type.simple_ty id
  | PIf of program_predicate * program * program
  | PEvent of program_event * program
  | PNonDet of program * program
  | PApp of program * program
  | PAppInt of program * arith_expr
  (* | PAbs of id * program *)
[@@deriving eq,ord,show]
and arith_expr =
    AVar of [`Int] id
  | AInt of int
  | AOp of arith_op * arith_expr list
[@@deriving eq,ord,show]
and program_predicate =
  | Pred of pred_op * arith_expr list 
  | And of program_predicate * program_predicate
  | Or of program_predicate * program_predicate
  | Bool of bool
[@@deriving eq,ord,show]

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
    | PNonDet (p1, p2) -> "if * then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> (Id.to_string ~without_id:true v)
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ " " ^ show_op op ^ " " ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
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
    | PVar s -> replace_var_name (Id.to_string ~without_id:true s)
    | PIf (p, p1, p2) -> "if " ^ go_predicate p ^ " then (" ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PEvent (pe, p) -> "event \"" ^ pe ^ "\"; " ^ go_program p
    | PNonDet (p1, p2) -> "if read_int () then ("  ^ go_program p1 ^ ") else (" ^ go_program p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go_program p1 ^ " " ^ go_program p2 ^ ")"
    | PAppInt (p1, a) -> "(" ^ go_program p1 ^ " " ^ go_arith a ^ ")"
  and go_arith p = match p with
    | AVar v -> replace_var_name (Id.to_string ~without_id:true v)
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ show_op op ^ go_arith arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
  and go_predicate p = match p with
    | Pred (op, [arg1; arg2]) -> "(" ^ go_arith arg1 ^ show_pred op ^ go_arith arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go_predicate p1 ^ " && " ^ go_predicate p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go_predicate p1 ^ " || " ^ go_predicate p2 ^ ")"
    | Bool b -> string_of_bool b
  in
  go_program p
  
type func = {
  var: Type.simple_ty id;
  args: Type.simple_argty id list;
  body: program
}
[@@deriving eq,ord,show]

type hes = program * func list
[@@deriving eq,ord,show]

let show_hes ((entry, hes) : hes) = 
  "let () = " ^ show_program entry ^ "\n" ^
  (List.map (fun {var; args; body} -> "let " ^ Id.to_string ~without_id:true var ^ " " ^ (String.concat " " (List.map (fun {Id.name; ty} -> "(" ^ name ^ ": " ^ show_simple_argty ty ^ ")") args)) ^ " = " ^ show_program body) hes |>
  String.concat "\n")
  

let show_hes_as_ocaml ((entry, hes) : hes) = 
  "let read_int () = read_int () != 0\n" ^
  "let event a = print_string a\n" ^
  (List.mapi (fun i {var; args; body} -> (if i = 0 then "let " else "and ") ^ (replace_var_name (Id.to_string var ~without_id:true)) ^ " " ^ (String.concat " " (List.map (fun {Id.name; ty} -> "(" ^ replace_var_name name ^ ": " ^ show_simple_argty ty ^ ")") args)) ^ " = " ^ show_program_as_ocaml body) hes |>
  String.concat "\n") ^ "\n" ^
  "let () = " ^ show_program_as_ocaml entry
  
let convert (raw : Raw_program.raw_program) var_env pred_env : program =
  let rec go_prog (raw : Raw_program.raw_program) : program = match raw with
    | PUnit -> PUnit
    | PVar id -> begin
      match List.find_opt (fun p -> p.Id.name = id) pred_env with
      | Some p -> PVar p
      | None -> begin
        match List.find_opt (fun p -> p.Id.name = id) var_env with
        | Some p -> begin
          match p.ty with
          | Type.TySigma t -> PVar { p with ty = t }
          | _ -> failwith @@ "convert PVar 3. Type-mismatch: should not be int type (name=" ^ id ^ ")"
        end
        | None -> failwith @@ "convert PVar 1 (name=" ^ id ^ ")"
      end
    end
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
    | PVar v -> begin
      match List.find_opt (fun p -> p.Id.name = v) var_env with
      | Some p -> AVar ({ p with ty=`Int })
      | None -> failwith @@ "convert PVar 2 (name=" ^ v ^ ")"
    end
    | _ -> failwith "go_arith"
  in
  go_prog raw

let to_funty args =
  let rec go args = match args with
    | [] -> Type.TyBool ()
    | x::xs -> Type.TyArrow ({ty=x; name=""; id=0}, go xs) in
  go args
    
let convert_all (raw : Raw_program.hes) = 
  let pred_args =
    List.map (
      fun {Raw_program.var; args; body} ->
        let ty = to_funty (List.map (fun (_, t) -> t) args) in
        let var_id = Id.gen ~name:var ty in
        let args = List.map (fun (name, t) -> Id.gen ~name:name t) args in
        (var_id, args, body)
     ) raw in
  let preds = List.map (fun (a, _, _) -> a) pred_args |> List.filter (fun a -> a.Id.name <> "") in
  let program_funcs =
    List.map (
      fun (var, args, body) ->
        let body = convert body args preds in
        {var; args; body}
    ) pred_args in
  match program_funcs |> List.partition (fun {var;_} -> var.Id.name = "")
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
  
let replace_var_name_with_upper v func_names =
  let func_names = List.map (fun {Id.name} -> name) func_names in
  match List.find_opt ((=)v) func_names with
  | None -> replace_var_name v
  | Some _ -> replace_var_name v |> to_uident

let replace_var_name_with_upper_var v func_names =
  let {Id.name; id; ty} = v in
  let name = replace_var_name_with_upper name func_names in
  {Id.name; id; ty}

let to_hflz_from_function program func_names =
  let rec go_program program: 'a Hflz.t = match program with
    | PUnit -> Bool true
    | PVar v -> Var (replace_var_name_with_upper_var v func_names)
    | PIf (p, p1, p2) ->
      And (
        Or (
          Hflz.negate_formula (go_predicate p),
          go_program p1
        ),
        Or (
          go_predicate p,
          go_program p2
        )
      )
    | PEvent (_, p) -> go_program p
    | PNonDet (p1, p2) ->
      And (
        go_program p1,
        go_program p2
      )
    | PApp (p1, p2) ->
      App (go_program p1, go_program p2)
    | PAppInt (p1, a) -> 
      App (go_program p1, Arith (go_arith a))
  and go_arith p : Arith.t  = match p with
    | AVar v -> Var (replace_var_name_with_upper_var v func_names)
    | AInt i -> Int i
    | AOp (op, [arg1; arg2]) ->
      Op (op, [go_arith arg1; go_arith arg2])
    | AOp _ -> failwith "to_hflz: go_arith"
  and go_predicate p : 'a Hflz.t = match p with
    | Pred (op, [arg1; arg2]) -> Pred (op, [go_arith arg1; go_arith arg2])
    | Pred _ -> failwith "to_hflz: go_predicate"
    | And (p1, p2) -> And (go_predicate p1, go_predicate p2)
    | Or (p1, p2) -> Or (go_predicate p1, go_predicate p2)
    | Bool b -> Bool b
  in
  go_program program

let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args
    
let to_hflz hes priority =
  let entry, hes = hes in
  if List.length hes <> List.length priority then failwith "to_hflz";
  let func_names = List.map (fun {var;_} -> var) hes in
  let hes = List.map (fun ({var; _} as p) ->
    match List.find_opt (fun (v, pr) -> Id.eq v var) priority with
    | None -> failwith "to_hflz (2)"
    | Some pr -> (snd pr, p)) hes in
  let hes = List.sort (fun (pr, _) (pr', _) -> compare pr pr') hes |> List.rev in
  let entry = to_hflz_from_function entry func_names in
  let rules =
    List.map (fun (pr, {var; args; body}) ->
      let fix = if pr mod 2 = 0 then Fixpoint.Greatest else Fixpoint.Least in
      {
        Hflz.var = replace_var_name_with_upper_var var func_names;
        fix;
        body =
          let args = List.map (fun a -> replace_var_name_with_upper_var a func_names) args in
          to_abs'
            args
            (to_hflz_from_function body func_names) 
      }
    ) hes in
  (entry, rules)
  