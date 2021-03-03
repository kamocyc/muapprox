open Program
open Hflmc2_syntax
open Itype
open Common_type
open Print_syntax

let convert (raw : Raw_program.raw_expression) var_env pred_env : program_expr =
  let rec go_prog (raw : Raw_program.raw_expression) : program_expr = match raw with
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
  and go_pred (raw : Raw_program.raw_expression) : program_predicate = match raw with
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
    | And (p1, p2) -> And (go_pred p1, go_pred p2)
    | Or (p1, p2) -> Or (go_pred p1, go_pred p2)
    | Bool b -> Bool b
    | _ -> failwith "go_pred"
  and go_arith (raw : Raw_program.raw_expression) : arith_expr = match raw with
    | AOp (op, ps) -> AOp (op, List.map go_arith ps)
    | AInt i -> AInt i
    | PVar v -> begin
      match List.find_opt (fun p -> p.Id.name = v) var_env with
      | Some p -> AVar ({ p with ty=`Int })
      | None -> failwith @@ "convert PVar 2 (name=" ^ v ^ ")"
    end
    | ANonDet -> ANonDet None
    | _ -> failwith "go_arith"
  in
  go_prog raw

let to_funty args =
  let rec go args = match args with
    | [] -> Type.TyBool ()
    | x::xs -> Type.TyArrow ({ty=x; name=""; id=0}, go xs) in
  go args
    
let convert_all (raw : Raw_program.raw_program) = 
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

let to_uident v =
  let c = String.get v 0 in
  (Char.uppercase_ascii c |> String.make 1) ^ String.sub v 1 (String.length v - 1)
  
let replace_var_name_with_upper v func_names =
  let func_names = List.map (fun {Id.name} -> name) func_names in
  match List.find_opt ((=)v) func_names with
  | None -> Print_syntax.replace_var_name v
  | Some _ -> Print_syntax.replace_var_name v |> to_uident

let replace_var_name_with_upper_var v func_names =
  let {Id.name; id; ty} = v in
  let name = replace_var_name_with_upper name func_names in
  {Id.name; id; ty}

let to_forall args body =
  let rec go = function
    | [] -> body
    | arg::xs -> Hflz.Forall(arg, go xs) in
  go args
  
let to_hflz_from_function program func_names =
  let idMap = Hashtbl.create 10 in
  let rec get_forall_vars prog = match prog with
    | PUnit | PVar _ -> prog
    | PIf (p, p1, p2) -> PIf (p, get_forall_vars p1, get_forall_vars p2)
    | PEvent (p, p1) -> PEvent (p, get_forall_vars p1)
    | PNonDet (p1, p2) -> PNonDet (get_forall_vars p1, get_forall_vars p2)
    | PApp (p1, p2) -> PApp (get_forall_vars p1, get_forall_vars p2)
    | PAppInt (p1, ANonDet _) ->
      let id = Id.gen ~name:"forall_x" Type.TyInt in
      Hashtbl.add idMap id.id id;
      PAppInt (get_forall_vars p1, ANonDet (Some id.id))
    | PAppInt (p1, p2) -> PAppInt (get_forall_vars p1, p2)
  in
  let program = get_forall_vars program in
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
    | PAppInt (p1, ANonDet idn_opt) -> begin
      match idn_opt with
      | Some idn ->
        let id = Hashtbl.find idMap idn in
        App (go_program p1, Arith (Var {id with ty=`Int}))
      | None -> assert false      
    end
    | PAppInt (p1, a) -> 
      App (go_program p1, Arith (go_arith a))
  and go_arith p : Arith.t  = match p with
    | AVar v -> Var (replace_var_name_with_upper_var v func_names)
    | AInt i -> Int i
    | ANonDet _ -> assert false
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
  let forall_bounded_vars = Hashtbl.fold (fun k v acc -> v::acc) idMap [] in
  to_forall
    forall_bounded_vars
    (go_program program)

let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args
    
let to_hflz prog priority =
  let entry, funcs = prog in
  if List.length funcs <> List.length priority then failwith "to_hflz";
  let func_names = List.map (fun {var;_} -> var) funcs in
  let funcs = List.map (fun ({var; _} as p) ->
    match List.find_opt (fun (v, pr) -> Id.eq v var) priority with
    | None -> failwith "to_hflz (2)"
    | Some pr -> (snd pr, p)) funcs in
  let funcs = List.sort (fun (pr, _) (pr', _) -> compare pr pr') funcs |> List.rev in
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
    ) funcs in
  (entry, rules)
  