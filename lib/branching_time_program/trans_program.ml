open Raw_program
open Program

let nullary_terminal = "nullary"

let capitalize_first s =
  match s with
  | "" -> ""
  | s ->
    let first = String.sub s 0 1 in
    let second = String.sub s 1 (String.length s - 1) in
    (String.capitalize_ascii first) ^ second

let gen_id ~name ty = 
  let id = Hflmc2_syntax.Id.gen `Int in
  {Hflmc2_syntax.Id.name = (if name = "" then "x" else name) ^ string_of_int id.id; id = id.id; ty = ty}
  
let get_first_nondet_arith (a : arith_expr) =
  let found = ref None in
  let rec go a = match a with
    | AVar v -> a
    | AInt i -> a
    | AOp (op, es) -> AOp (op, List.map go es)
    | ANonDet (_, e) -> begin
      match !found with
      | Some f -> a
      | None -> begin
        let id = gen_id ~name:"x" `Int in
        found := Some (id, e);
        AVar id
      end
    end
  in
  let a = go a in
  a, !found

let get_first_nondet_formula (f : program_predicate) =
  let rec go expr = match expr with
    | Bool _ -> []
    | Or (e1, e2) -> go e1 @ go e2
    | And (e1, e2) -> go e1 @ go e2
    | Pred (p, a) ->
      List.map get_first_nondet_arith a
  in
  match go f with
  | [] -> None
  | x::xs -> begin
    match snd x with
    | None -> None
    | Some (a, b) -> Some a
  end

let get_type (expr : program_expr) =
  let open Hflmc2_syntax in
  let rec go expr = match expr with
    | PUnit -> Type.TyBool ()
    | PVar v -> v.ty
    | PIf (p, e1, e2) -> begin
      let ty1 = go e1 in
      let ty2 = go e2 in
      assert (ty1 = ty2);
      ty1
    end
    | PEvent (_, e1) -> go e1
    | PNonDet (e1, e2, _, _) ->
      let ty1 = go e1 in
      let ty2 = go e2 in
      assert (ty1 = ty2);
      ty1
    | PApp (e1, e2) -> begin
      let ty1 = go e1 in
      let ty2 = go e2 in
      match ty1 with
      | Type.TyArrow (argty, ty1') -> begin
        match argty.ty with
        | Type.TySigma ty -> 
          assert (ty = ty2);
          ty1'
        | Type.TyInt -> failwith "get_type (should not be int)"
      end
      | Type.TyBool () -> failwith "get_type"
    end
    | PAppInt (e1, a1) -> begin
      let ty1 = go e1 in
      match ty1 with
      | Type.TyArrow (argty, ty1') -> begin
        match argty.ty with
        | Type.TyInt -> ty1'
        | Type.TySigma _ -> failwith "get_type (should be int)"
      end
      | Type.TyBool () -> failwith "get_type"
    end
  in
  go expr

let type_check_expr ?check_env expr = 
  let open Hflmc2_syntax in
  let rec go expr = match expr with
    | Horsz.PVar v -> begin
      (match check_env with
      | None -> ()
      | Some env -> begin
        match List.find_all (Hflmc2_syntax.Id.eq v) env with
        | [] -> failwith @@ "unbounded: " ^ v.name
        | [x] -> begin
          match x.ty with
          | Type.TySigma ty ->
            assert (ty = v.ty)
          | Type.TyInt -> failwith @@ "illegal bounded type: " ^ v.name
        end
        | _ ->  failwith @@ "many: " ^ v.name
      end);
      v.ty
    end
    | App (p1, p2) -> begin
      let ty1 = go p1 in
      let ty2 = go p2 in
      match ty1 with
      | Type.TyArrow (argty, ty1') -> begin
        match argty.ty with
        | Type.TySigma ty -> 
          assert (ty = ty2);
          ty1'
        | Type.TyInt -> failwith @@ "type_check_expr (should not be int), expr=" ^ Horsz.show_horsz_expr_s expr
      end
      | Type.TyBool () -> failwith "type_check_expr"
    end
    | AppInt (p1, a1) -> begin
      (match check_env with
      | None -> ()
      | Some env -> go_arith env a1);
      let ty1 = go p1 in
      match ty1 with
      | Type.TyArrow (argty, ty1') -> begin
        match argty.ty with
        | Type.TyInt -> ty1'
        | Type.TySigma _ -> failwith @@ "type_check_expr (should be int), expr=" ^ Horsz.show_horsz_expr_s expr
      end
      | Type.TyBool () -> failwith "type_check_expr"      
    end
    | If (p, p1, p2) -> begin
      (match check_env with
      | None -> ()
      | Some env -> go_predicate env p);
      let ty1 = go p1 in
      let ty2 = go p2 in
      assert (ty1 = ty2);
      ty1
    end
    | Terminal _ ->
      Type.TyBool ()
  and go_predicate env f = match f with
    | Pred (_, a) -> List.iter (go_arith env) a
    | And (p1, p2) -> go_predicate env p1; go_predicate env p1
    | Or (p1, p2) -> go_predicate env p1; go_predicate env p1
    | Bool _ -> ()
  and go_arith env a1 = match a1 with
    | AVar v -> begin
      match (List.find_all (Id.eq v) env) with
      | [] -> failwith @@ "unbounded: " ^ v.name
      | [x] ->
        assert (x.ty = Type.TyInt);
        ()
      | _ -> failwith @@ "many: " ^ v.name
    end
    | Int _ -> ()
    | Op (_, a) -> List.iter (go_arith env) a
  in
  go expr

let type_check_horsz horsz =
  let global_env = List.map (fun {Horsz.var; args; body} -> {var with ty = Hflmc2_syntax.Type.TySigma (var.ty)}) (snd horsz) in
  let (entry, rules) = horsz in
  ignore @@ type_check_expr ~check_env:global_env entry;
  List.iter (fun {Horsz.var; args; body} ->
    ignore @@ type_check_expr ~check_env:(global_env @ args) body
  ) rules
  
let get_free_variables expr =
  let open Hflmc2_syntax in
  let rec go expr = match expr with
    | PUnit -> []
    | PVar v -> [{v with ty=Type.TySigma (v.ty)}]
    | PIf (f1, e1, e2) -> go_formula f1 @ go e1 @ go e2
    | PEvent (_, e) -> go e
    | PNonDet (e1, e2, _, _) -> go e1 @ go e2
    | PApp (e1, e2) -> go e1 @ go e2
    | PAppInt (e1, a1) -> go e1 @ go_arith a1
  and go_formula f1 = match f1 with
    | Pred (_, a) -> List.map go_arith a |> List.flatten
    | And (f1, f2) -> go_formula f1 @ go_formula f2
    | Or (f1, f2) -> go_formula f1 @ go_formula f2
    | Bool _ -> []
  and go_arith a1 = match a1 with
    | AVar v -> [{v with ty=Type.TyInt}]
    | AInt _ -> []
    | AOp (_, a) -> List.map go_arith a |> List.flatten
    | ANonDet _ -> []
  in
  go expr

let to_funty args =
  let open Hflmc2_syntax in
  let rec go args = match args with
    | [] -> Type.TyBool ()
    | x::xs -> Type.TyArrow ({ty=x; name=""; id=0}, go xs) in
  go args

let trans_non_det global_env expr var_id ev =
  let open Hflmc2_syntax in
  let ev = match ev with Some ev -> ev | None -> failwith "non-deterministic integer should have an event name" in
  let ty = get_type expr in
  let cont =
    gen_id ~name:"k" (Type.TyArrow ({name=""; id=0; ty=Type.TyInt}, ty)) in
  let rec_id = gen_id ~name:"Integer" (Type.TyArrow ({name=""; id=0; ty=Type.TyInt}, Type.TyArrow ({name=""; id=0; ty=Type.TySigma cont.Id.ty}, ty))) in
  let body =
    Horsz.Terminal (
      ev,
      [
        AppInt (PVar cont, AVar var_id);
        App (
          AppInt (
            PVar rec_id, Op (Add, [AVar var_id; Int 1])
          ),
          PVar cont
        );
        App (
          AppInt (
            PVar rec_id, Op (Sub, [AVar var_id; Int 1])
          ),
          PVar cont
        );
      ]
    )
  in
  let new_horsz_rule = {Horsz.var = rec_id; args = [{var_id with ty=Type.TyInt}; {cont with ty=Type.TySigma (cont.ty)}]; body} in
  let free_variables =
    get_free_variables expr
    |> List.filter (fun v -> (not @@ List.exists (fun v' -> Id.eq v v') global_env) && (not @@ Id.eq v var_id))
  in
  let args = free_variables @ [{var_id with ty=Type.TyInt}] in
  let funty = to_funty (List.map (fun i -> i.Id.ty) args) in
  let var = gen_id (capitalize_first ev ^ "_sub") funty in
  let new_rule = {var; args; body = expr} in
  let org_body =
    let rec g ls = match ls with
      | [] -> Horsz.PVar var
      | x::xs -> begin
        match x.Id.ty with
        | Type.TySigma t -> App (g xs, PVar {x with ty = t})
        | Type.TyInt -> AppInt (g xs, AVar {x with ty = `Int})
      end in
    g (free_variables |> List.rev) in
  Horsz.App (
    AppInt (PVar rec_id, Int 0),
    org_body
  ),
  new_horsz_rule,
  new_rule,
  (ev, 3)

let decompose_anondet global_env expr =
  let found = ref None in
  let rec go expr = match expr with
    | PVar v -> PVar v
    | PApp (e1, e2) -> PApp (go e1, go e2)
    | PAppInt (e1, a2) -> PAppInt (go e1, go_arith a2)
    | _ -> failwith "decompose_anondet"
  and go_arith arith = match arith with
    | AVar v -> arith
    | AInt i -> arith
    | AOp (op, es) -> AOp (op, List.map go_arith es)
    | ANonDet (_, e) -> begin
      match !found with
      | Some f -> arith
      | None -> begin
        let id = gen_id ~name:"x" `Int in
        found := Some (id, e);
        AVar id
      end
    end
  in
  let expr = go expr in
  match !found with
  | None -> None
  | Some (var_id, ev) -> begin
    Some (trans_non_det global_env expr var_id ev)
  end

let trans (program: program) =
  let new_rules = ref [] in
  let used_terminals = ref [] in
  let global_env = List.map (fun {var; args; body} -> var) (snd program) in
  let rec go_expr (expr : program_expr) = match expr with
    | PUnit ->
      used_terminals := (nullary_terminal, 0)::!used_terminals;
      Horsz.Terminal (nullary_terminal, [])
    | PVar v -> begin
      if List.exists (Hflmc2_syntax.Id.eq v) global_env then
        PVar { v with name = capitalize_first v.name }
      else
        PVar v
    end
    | PIf (pred, e1, e2) -> begin
      let id_expr_opt = get_first_nondet_formula pred in
      match id_expr_opt with
      | None -> If (go_pred pred, go_expr e1, go_expr e2)
      | Some _ -> failwith "non-deterministic integer in if-expression condition is currently unsupported. Please use a variable and application"
    end
    | PEvent (e, e1) ->
      used_terminals := (e, 1)::!used_terminals;
      Terminal (e, [go_expr e1])
    | PNonDet (e1, e2, _, e) -> begin
      match e with
      | Some e ->
        used_terminals := (e, 2)::!used_terminals;
        Terminal (e, [go_expr e1; go_expr e2])
      | None -> failwith "non-deterministic choice needs event name"
    end
    | PApp (e1, e2) -> begin
      match decompose_anondet global_env expr with
      | Some (expr, recur_rule, lambda_lifted_rule, used_terminal) -> 
        let lambda_lifted_rule =
          { Horsz.var = lambda_lifted_rule.var;
            args = lambda_lifted_rule.args;
            body = go_expr lambda_lifted_rule.body } in
        new_rules := recur_rule :: lambda_lifted_rule :: !new_rules;
        used_terminals := used_terminal::!used_terminals;
        expr
      | None ->
        App (go_expr e1, go_expr e2)
    end
    | PAppInt (e1, a1) -> begin
      match decompose_anondet global_env expr with
      | Some (expr, recur_rule, lambda_lifted_rule, used_terminal) -> 
        let lambda_lifted_rule =
          { Horsz.var = lambda_lifted_rule.var;
            args = lambda_lifted_rule.args;
            body = go_expr lambda_lifted_rule.body } in
        new_rules := recur_rule :: lambda_lifted_rule :: !new_rules;
        used_terminals := used_terminal::!used_terminals;
        expr
      | None ->
        AppInt (go_expr e1, go_arith a1)
    end
  and go_pred (pred : program_predicate) = match pred with
    | Pred (op, es) -> Pred (op, List.map go_arith es)
    | Or (e1, e2) -> Or (go_pred e1, go_pred e2)
    | And (e1, e2) -> And (go_pred e1, go_pred e2)
    | Bool b -> Bool b
  and go_arith (arith : arith_expr) = match arith with
    | AVar v -> AVar v
    | AInt i -> Int i
    | AOp (op, es) -> Op (op, List.map go_arith es)
    | ANonDet (_, e) -> failwith "go_arith (anondet)"
  in
  let (entry, rules) = program in
  let entry = go_expr entry in
  let rules = List.map (fun {var; args; body} ->
    let body = go_expr body in
    {Horsz.var = {var with name = capitalize_first var.name}; args; body}
  ) rules in
  let used_terminals = Hflmc2_util.remove_duplicates ((=)) !used_terminals in
  let horsz = (entry, rules @ !new_rules) in
  (* print_endline "before typecheck";
  Horsz.print horsz false; *)
  type_check_horsz horsz;
  (horsz, used_terminals)
