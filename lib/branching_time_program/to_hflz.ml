open Hflmc2_syntax
open Util
module A = AlternatingAutomaton

let make_name org_name state priority =
  org_name ^ "__" ^ state ^ "__" ^ string_of_int priority

let get_states_times_prs all_states max_priority = list_product all_states (upto max_priority)

let make_apps p1 args =
  let rec go = function
    | [] -> p1
    | x::xs -> Hflz.App (go xs, x)
  in
  go (List.rev args)

let rec make_ands : 'a Hflz.t list -> 'a Hflz.t = function
  | [] -> failwith "make_ands"
  | [x] -> x
  | x::xs -> And (x, make_ands xs)

let rec make_ors : 'a Hflz.t list -> 'a Hflz.t = function
  | [] -> failwith "make_ands"
  | [x] -> x
  | x::xs -> Or (x, make_ors xs)

let trans_ty all_states max_priority ty =
  let states_times_prs = get_states_times_prs all_states max_priority in
  let rec trans_argty ty = match ty with
    | Type.TySigma ty -> Type.TySigma (trans_ty ty)
    | Type.TyInt -> ty
  and trans_ty ty = match ty with
    | Type.TyArrow (arg, body) ->
      let body = trans_ty body in
      let args =
        match arg.ty with
        | Type.TyInt -> [arg.ty]
        | Type.TySigma _ -> 
          List.map (fun _ ->
            trans_argty arg.ty
          ) states_times_prs in
      let rec go body args = match args with
        | [] -> body
        | arg::args -> Type.TyArrow ({name=""; id=0; ty=arg}, go body args)
      in
      go body args
    | Type.TyBool a -> Type.TyBool a
  in
  trans_ty ty

let trans_argty all_states max_priority ty =
  match ty with
  | Type.TySigma ty -> Type.TySigma (trans_ty all_states max_priority ty)
  | Type.TyInt -> ty

let trans_body automaton all_states max_priority global_env rule_args current_state (phi : 'a Horsz.horsz_expr) =
  let states_times_prs = get_states_times_prs all_states max_priority in
  let rec go (env :  'a Hflmc2_syntax.Type.arg Hflmc2_syntax.Id.t list) state pr_m (phi : 'a Horsz.horsz_expr): 'a Hflz.t = match phi with
    | PVar v -> begin
      let name = make_name v.Id.name state pr_m in
      match List.find_all (fun id -> id.Id.name = name) env with
      | [id] -> begin
        match id.Id.ty with
        | Type.TySigma (ty) -> Var { id with Id.ty = ty }
        | TyInt -> failwith "trans_body"
      end
      | [] -> failwith @@ "not found: " ^ name
      | _ -> assert false
    end
    | App (p1, p2) -> begin
      let args =
        List.map
          (fun (st, m) -> (st, max pr_m m)) states_times_prs
        |> List.map (fun (st, m) ->
          go env st m p2
        )
        in
      let p1 = go env state pr_m p1 in
      make_apps p1 args
    end
    | AppInt (p1, p2) -> begin
      let p1 = go env state pr_m p1 in
      let p2 = Hflz.Arith (go_arith env p2) in
      App (p1, p2)
    end
    | If (p1, p2, p3) -> begin
      let cond = go_formula env p1 in
      let p2 = go env state pr_m p2 in
      let p3 = go env state pr_m p3 in
      Or (
        And (
          cond,
          p2
        ),
        And (
          Hflz.negate_formula cond,
          p3
        )
      )
    end
    | Terminal (c, ts) -> begin
      let transitions = A.get_transition automaton state c in
      let f =
        match transitions with
        | [] -> Hflz.Bool false
        | transitions -> begin
          List.map
            (fun clause ->
              (* clause is conjunction of literals *)
              match clause with
              | [] -> Hflz.Bool true
              | clause ->
                List.map
                  (fun (A.CVar (d', q')) ->
                    let m' = max pr_m (A.get_prioirty automaton q')in
                    match List.nth_opt ts (d' - 1) with
                    | Some t -> go env q' m' t
                    | None ->
                      failwith @@
                        "terminal not found: symbol=" ^ c ^ ", " ^
                        "index=" ^ string_of_int (d' - 1) ^ "," ^
                        "term=" ^ Horsz.show_horsz_expr_s phi
                    (* go env q' m' ps *)
                  )
                  clause
                |> make_ands
            )
            transitions
            |> make_ors
        end in
      f
    end
  and go_formula env phi = match phi with
    | Bool b -> Hflz.Bool b
    | Or (p1, p2) -> Or (go_formula env p1, go_formula env p2)
    | And (p1, p2) -> And (go_formula env p1, go_formula env p2)
    | Pred (p, ps) -> Pred (p, List.map (go_arith env) ps)
  and go_arith env phi = match phi with
    | Int i -> Arith.Int i
    | AVar v -> begin
      match List.find_all (fun id -> id.Id.name = v.Id.name) env with
      | [id] -> begin
        Var { id with ty = `Int }
      end
      | [] -> failwith @@ "not found: " ^ v.Id.name
      | _ -> assert false
    end
    | Op (o, ps) -> Op (o, List.map (go_arith env) ps)
  in
  let env = (List.map (fun id -> { id with Id.ty = Type.TySigma id.Id.ty }) global_env) @ rule_args in
  (* state pr_m *)
  go env current_state 0 phi

let trans_horsz automaton horsz =
  let {A.st; omega; init = initial_state} = automaton in
  let all_states = st in
  let max_priority = List.fold_left (fun a (_, b) -> max a b) 0 omega in
  let (entry, rules) = horsz in
  (* generate ids *)
  let rules =
    List.map
      (fun m ->
        List.map (fun {Horsz.var; body; args} ->
          List.map (fun q ->
            let states_times_prs = get_states_times_prs all_states max_priority in
            (* arguments *)
            let args =
              List.map (fun arg ->
                match arg.Id.ty with
                | Type.TyInt ->
                  [Id.gen ~name:arg.Id.name arg.Id.ty]
                | Type.TySigma _ ->
                  List.map
                    (fun (a, b) ->
                      let name = make_name arg.Id.name a b in
                      let ty = trans_argty all_states max_priority (arg.Id.ty) in
                      Id.gen ~name:name ty
                    )
                    states_times_prs
              ) args 
              |> List.flatten in
            let name = make_name var.Id.name q m in
            let ty = trans_ty all_states max_priority var.Id.ty in
            let var = Id.gen ~name:name ty in
            ({Horsz.var; body; args}, m, q)
          ) all_states
        )
        rules
        |> List.flatten
      )
      (upto max_priority |> List.rev)
      |> List.flatten in
  let global_env = List.map (fun ({Horsz.var}, _, _) -> var) rules in
  let entry = trans_body automaton all_states max_priority global_env [] initial_state entry in
  let rules =
    List.map (fun ({Horsz.var; body; args}, m, q) ->
      let body = trans_body automaton all_states max_priority global_env args q body in
      let fix =
        if m mod 2 = 0 then Fixpoint.Greatest else Least in
      let rec go body args = match args with
        | [] -> body
        | arg::args -> Hflz.Abs (arg, go body args) in
      let body = go body args in
      {Hflz.var; body; fix}
    ) rules in
  let hes = (entry, rules) in
  Manipulate.Hflz_typecheck.type_check hes;
  hes