open Hflmc2_syntax
open Horsz
open Util
  
let to_hors_expr env terminals body =
  let module R = Raw_horsz in
  let rec go phi = match phi with
    | R.PVar (s, n) -> begin
      assert (n = None);
      match List.find_all (fun n -> s = n.Id.name) env with
      | [id] -> begin
        match id.ty with
        | Type.TySigma t -> PVar { id with ty = t }
        | _ -> failwith @@ "convert PVar 3. Type-mismatch: should not be int type (name=" ^ Id.to_string id ^ ")"
      end
      | [] -> begin
        match List.find_all (fun (n', i) -> s = n') terminals with
        | [(t, i)] -> begin
          if i <> 0 then failwith "illegal use of terminal";
          Terminal (t, [])
        end
        | [] -> failwith @@ "unbounded: " ^ s
        | _ -> assert false
      end
      | _ -> assert false
    end
    | PIf (p1, p2, p3) -> begin
      If (go_formula p1, go p2, go p3)
    end
    | PApp (p1, p2) -> begin
      let r =
        let rec agg_args acc p = match p with
          | R.PApp (p1, p2) -> (agg_args (p2 :: acc) p1)
          | PVar (s, n) -> Some ((s, n), acc)
          | _ -> None in
        match agg_args [] phi with
        | None -> None
        | Some ((s, n), args) -> begin
          assert (n = None);
          (match List.find_all (fun (n', i) -> s = n') terminals with
          | [(t, _)] -> begin
            (* TODO:  *)
            let args = List.map go args in
            Some (Terminal (t, args))
          end
          | [] -> None
          | _ -> assert false)
        end
      in
      match r with
      | None -> begin
        let p1 = go p1 in
        try
          App (p1, go p2)
        with _ -> AppInt (p1, go_arith p2)
      end
      | Some r -> r
    end
    | AInt _ -> assert false
    | AOp _ -> assert false
    | Pred _ -> assert false
    | And _ -> assert false
    | Or _ -> assert false
  and go_arith phi = match phi with
    | R.PVar (s, n) -> begin
      assert (n = None);
      match List.find_all (fun n -> s = n.Id.name) env with
      | [id] -> begin
        match id.ty with
        | Type.TyInt -> AVar { id with ty = `Int }
        | _ -> failwith @@ "convert AVar 3. Type-mismatch: should be int type (name=" ^ Id.to_string id ^ ")"
      end
      | [] -> failwith @@ "unbounded: " ^ s
      | _ -> assert false
    end
    | AInt n -> Int n
    | AOp (op, xs) ->
      Op (op, List.map go_arith xs)
    | _ -> failwith "go_arith"
  and go_formula phi = match phi with
    | R.And (p1, p2) -> And (go_formula p1, go_formula p2)
    | Or (p1, p2) -> Or (go_formula p1, go_formula p2)
    | Pred (p, xs) -> Pred (p, List.map go_arith xs)
    | _ -> failwith "go_formula"
  in
  go body

let to_horsz (terminals : (terminal * int) list) (raw : Raw_horsz.raw_program) =
  let module R = Raw_horsz in
  print_endline @@ R.show_raw_program raw;
  let (first, rules) =
    match raw with
    | first::rules -> begin
      (* (first, rules) *)
      let {R.var; args; body} = first in
      if List.length args <> 0 then failwith "first rule should not have arguments";
      (body, rules)
    end
    | [] -> failwith "no HORSz rules" in
  let rules =
    List.map (fun {R.var; args; body} ->
      let (name, o) = var in
      assert (o = None);
      let args =
        List.map (fun (s, ty) ->
          match ty with
          | None -> assert false
          | Some ty -> Id.gen ~name:s ty
        ) args in
      let rec go = function 
        | [] -> Type.TyBool ()
        | x::xs -> Type.TyArrow ({name=""; id=0; ty=x}, go xs)
      in
      let ty = go (List.map (fun {Id.ty} -> ty) args) in
      let v = Id.gen ~name:name ty in
      (v, args, body)
    ) rules in
  let global_env = List.map (fun (v, _, _) -> { v with Id.ty = Type.TySigma v.Id.ty }) rules in
  let entry = to_hors_expr global_env terminals first in
  let rules =
    List.map (fun (v, args, body) ->
      let env = global_env @ args in
      if contains_duplicates (List.map (fun id -> id.Id.name) env @ (List.map fst terminals)) then
        failwith "arguments, terminal and nonterminal name conflict";
      let body = to_hors_expr env terminals body in
      {var = v; args; body}
    ) rules in
  (entry, rules)
  