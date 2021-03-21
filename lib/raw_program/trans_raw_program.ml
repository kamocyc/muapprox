module R = Program_raw
open Hflmc2_syntax

type tv_expression = R.ptype Id.t R.raw_expression_gen
[@@deriving eq,ord,show]

type tv_function = R.ptype Id.t R.raw_function_gen
[@@deriving eq,ord,show]

type tv_program = R.ptype Id.t R.raw_program_gen
[@@deriving eq,ord,show]

let convert (raw : tv_expression) (var_env : Type.simple_argty Env.t) (pred_env : Type.simple_ty Env.t) : Program.program_expr =
  let rec go_prog (raw : tv_expression) : Program.program_expr = match raw with
    | PUnit -> PUnit
    | PVar id -> begin
      try
        let p = Env.lookup id pred_env in
        PVar p
      with
        Not_found -> begin
          let p = Env.lookup id var_env in
          match p.ty with
          | Type.TySigma t -> PVar { p with ty = t }
          | _ -> failwith @@ "convert PVar 3. Type-mismatch: should not be int type (name=" ^ Id.to_string id ^ ")"
        end
    end
    | PIf (p, p1, p2) -> PIf (go_pred p, go_prog p1, go_prog p2)
    | PEvent (pe, p) -> PEvent (pe, go_prog p)
    | PNonDet (p1, p2) -> PNonDet (go_prog p1, go_prog p2, None)
    | PApp (p1, p2) -> begin
      let p1 = go_prog p1 in
      try
        PApp (p1, go_prog p2)
      with _ -> PAppInt (p1, go_arith p2)
    end
    | _ -> failwith "go_prog"
  and go_pred (raw : tv_expression) : Program.program_predicate = match raw with
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
    | And (p1, p2) -> And (go_pred p1, go_pred p2)
    | Or (p1, p2) -> Or (go_pred p1, go_pred p2)
    | Bool b -> Bool b
    | _ -> failwith "go_pred"
  and go_arith (raw : tv_expression) : Program.arith_expr = match raw with
    | AOp (op, ps) -> AOp (op, List.map go_arith ps)
    | AInt i -> AInt i
    | PVar v ->
      let p = Env.lookup v var_env in
      AVar ({ p with ty=`Int })
    | ANonDet -> ANonDet None
    | _ -> failwith @@ "go_arith: " ^ show_tv_expression raw
  in
  go_prog raw

let to_funty args =
  let rec go args = match args with
    | [] -> R.TUnit
    | x::xs -> R.TFunc (x, go xs) in
  go args
  
let get_free_variables (phi : tv_expression) : R.ptype Env.t =
  let rec go_expr (phi : tv_expression) = match phi with
    | PUnit | AInt _ | Bool _ | ANonDet -> Env.create []
    | PVar v -> Env.create [v]
    | PIf (p, p1, p2) -> Env.merge [go_expr p; go_expr p1; go_expr p2]
    | PEvent (_, p1) -> go_expr p1
    | PNonDet (p1, p2) -> Env.merge [go_expr p1; go_expr p2]
    | PApp (p1, p2) -> Env.merge [go_expr p1; go_expr p2]
    | AOp (_, ps) -> Env.merge (List.map go_expr ps)
    | Pred (_, ps) -> Env.merge (List.map go_expr ps)
    | And (p1, p2) -> Env.merge [go_expr p1; go_expr p2]
    | Or (p1, p2) -> Env.merge [go_expr p1; go_expr p2]
    | PLambda (args, p1) ->
      Env.remove args (go_expr p1)
    | _ -> assert false
  in
  go_expr phi

let lambda_lift_sub
    ?(base_name : string option)
    (global_env : R.ptype Env.t)
    (env : R.ptype Env.t)
    (phi : tv_expression)
    : tv_expression * tv_function list =
  let open R in
  let new_rules = ref [] in
  let gen_function_id ty =
    let base_name = 
      match base_name with
      | None -> "lam_"
      | Some n -> n in
    let id = Id.gen ty in
    { id with name = base_name ^ string_of_int id.id } in
  let rec go (phi : tv_expression) : tv_expression = match phi with
    | PLambda (args, body) -> begin
      let free_variables =
        Env.remove (Env.to_list global_env) (get_free_variables phi)
        |> Env.to_list
        |> List.map (fun v -> Env.lookup v env)
      in 
      let args = free_variables @ args in
      let funty = to_funty (List.map (fun i -> i.Id.ty) args) in
      let var = gen_function_id funty in      
      new_rules := {var; args; body}::!new_rules;
      let rec g ls : tv_expression = match ls with
        | [] -> PVar var
        | x::xs -> PApp (g xs, PVar x) in
      g (free_variables |> List.rev)
    end
    | PUnit | AInt _ | Bool _ | ANonDet | PVar _ -> phi
    | PIf (p, p1, p2) -> PIf (go p, go p1, go p2)
    | PEvent (e, p1) -> PEvent (e, go p1)
    | PNonDet (p1, p2) -> PNonDet (go p1, go p2)
    | PApp (p1, p2) -> PApp (go p1, go p2)
    | AOp (e, ps) -> AOp (e, List.map go ps)
    | Pred (e, ps) -> Pred (e, List.map go ps)
    | And (p1, p2) -> And (go p1, go p2) 
    | Or (p1, p2) -> Or (go p1, go p2) 
    | _ -> assert false
  in
  let phi = go phi in
  (phi, !new_rules)
  
let rec lambda_lift
    ?(base_name : string option)
    (global_env : R.ptype Env.t)
    (env : R.ptype Env.t)
    (phi : tv_expression)
    =
  let (phi, new_rules) = lambda_lift_sub ?base_name global_env env phi in
  let new_rules =
    List.map (fun ({var; args; body} : tv_function) ->
      let (body, new_rules') = lambda_lift ~base_name:var.Id.name global_env (Env.create args) body in
      {R.var; args; body} :: new_rules'
    ) new_rules
    |> List.flatten in
  (phi, new_rules)

let convert_let (phi : tv_expression) =
  let rec go (phi : tv_expression) = match phi with
    | PUnit | AInt _ | Bool _ | ANonDet | PVar _ -> phi
    | PLambda (args, body) -> PLambda (args, go body)
    | PIf (p, p1, p2) -> PIf (go p, go p1, go p2)
    | PEvent (e, p1) -> PEvent (e, go p1)
    | PNonDet (p1, p2) -> PNonDet (go p1, go p2)
    | PApp (p1, p2) -> PApp (go p1, go p2)
    | AOp (e, ps) -> AOp (e, List.map go ps)
    | Pred (e, ps) -> Pred (e, List.map go ps)
    | And (p1, p2) -> And (go p1, go p2) 
    | Or (p1, p2) -> Or (go p1, go p2)
    | PLet (x, p1, p2) ->
      PApp (PLambda ([x], go p2), go p1) in
  go phi

let has_prefix whole prefix =
  String.length whole >= String.length prefix &&
    String.sub whole 0 (String.length prefix) = prefix

let rec subst_ptype ptype subst =
  let open R in
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool | TUnit -> ptype
  | TFunc (p1, p2) -> TFunc (subst_ptype p1 subst, subst_ptype p2 subst)

let is_occur id ty =
  let rec go (ty : R.ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TBool | TUnit -> false
    | TFunc (p1, p2) -> go p1 || go p2 in
  go ty

let compose_subst (id, ty) subst =
  let ty' = subst_ptype ty subst in
  (id, ty') :: subst
  
let unify (constraints : (R.ptype * R.ptype) list) =
  let open R in
  let is_equal_ptype = (=) in
  let rec subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair], subst_ptype p2 [pair])) xs in
  let rec unify constraints = match constraints with
    | [] -> []
    | (t1, t2)::xs -> begin
      if is_equal_ptype t1 t2
      then unify xs
      else begin
        match t1, t2 with
        | TFunc (t11, t12), TFunc (t21, t22) ->
          unify ((t11, t21) :: (t12, t22) :: constraints)
        | TVar t11, t2 -> begin
          if is_occur t11 t2 then failwith "occur1";
          compose_subst (t11, t2) (unify (subst xs (t11, t2)))
        end
        | t1, TVar t21 -> begin
          if is_occur t21 t1 then failwith "occur2";
          compose_subst (t21, t1) (unify (subst xs (t21, t1)))
        end
        | _ ->
          failwith @@ "unify (left: " ^ show_ptype t1 ^ " / right: " ^ show_ptype t2 ^ ")"
      end
    end in
  (* print_endline "constraints:";
  print_endline @@ (Hflmc2_util.show_pairs show_ptype show_ptype constraints); *)
  let r = unify constraints in
  (* print_endline "unify:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_ptype r); *)
  r

let generate_constraints (raw : tv_program) : (R.ptype * R.ptype) list =
  let open R in
  let rec gen (env : R.ptype Env.t) (raw : tv_expression):
      ptype * (ptype * ptype) list
       = match raw with
    | PIf (p1, p2, p3) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let t3, c3 = gen env p3 in
      (t2, [(t1, TBool); (t2, t3)] @ c1 @ c2 @ c3)
    | PLambda (args, body) ->
      let t, c = gen (Env.update args env) body in
      let rec go base ls = match ls with
        | [] -> base
        | x::xs -> TFunc (x.Id.ty, go base xs) in
      (go t args, c)
    | PApp (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar)) :: c1 @ c2)
    | PUnit -> (TUnit, [])
    | AInt _ -> (TInt, [])
    | Bool _ -> (TBool, [])
    | ANonDet -> (TInt, [])
    | PVar v ->
      let id = Env.lookup v env in
      (id.ty, [])
    | PLet (x, p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen (Env.update [x] env) p2 in
      (t2, c1 @ c2)
    | PEvent (_, p) ->
      let t, c = gen env p in
      (t, c)
    | PNonDet (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (t1, (t1, t2) :: c1 @ c2)
    | AOp (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | Pred (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | And (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | Or (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2) in
  let global_env = List.map (fun {var} -> var) raw in
  let constraints =
    List.map
      (fun ({var; args; body} : tv_function) ->
        gen (Env.update args (Env.create global_env)) body |> snd
      )
      raw
    |> List.flatten in
  constraints

let subst_program (raw : tv_program) (subst : (unit Id.t * Program_raw.ptype) list) : tv_program =
  let open R in
  let rec go (raw : tv_expression) = match raw with
    | PUnit -> PUnit
    | AInt i -> AInt i
    | Bool b -> Bool b
    | PVar v -> PVar { v with ty = subst_ptype v.ty subst }
    | PIf (p1, p2, p3) -> PIf (go p1, go p2, go p3)
    | PEvent (e, p1) -> PEvent (e, go p1)
    | PNonDet (p1, p2) -> PNonDet (go p1, go p2)
    | PApp (p1, p2) -> PApp (go p1, go p2)
    | AOp (o, ps) -> AOp (o, List.map go ps)
    | Pred (o, ps) -> Pred (o, List.map go ps)
    | And (p1, p2) -> And (go p1, go p2)
    | Or (p1, p2) -> Or (go p1, go p2)
    | PLambda (args, body) ->
      PLambda (List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst }) args, go body)
    | PLet (v, p1, p2) ->
      PLet ({ v with ty = subst_ptype v.Id.ty subst }, go p1, go p2)
    | ANonDet -> ANonDet in
  List.map (fun {var; args; body} ->
    let var = { var with Id.ty = subst_ptype var.Id.ty subst } in
    let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty subst }) args in
    let body = go body in
    { var; args; body }
  ) raw
     
     
let infer_type (raw : tv_program) =
  let constraints = generate_constraints raw in
  let substitution = unify constraints in
  let raw = subst_program raw substitution in
  raw

let assign_id (raw : R.raw_program) : tv_program =
  let open R in
  let pred_args =
    List.map (
      fun {var; args; body} ->
        let args =
          List.map (fun (n, t) ->
              match t with
              | None -> n, TVar (Id.gen ())
              | Some t -> n, t
            ) args in
        let ty = to_funty (List.map snd args) in
        let var_id = Id.gen ~name:(fst var) ty in
        (* TODO: no duplication in arg or func names *)
        let args = List.map (fun (name, t) -> Id.gen ~name:name t) args in
        (var_id, args, body)
    ) raw in
  let global_env = List.map (fun (v, _, _) -> v) pred_args in
  let rec go (env : ptype Id.t list) (raw : raw_expression) = match raw with
    | PVar (v, _) -> begin
      match List.find_all (fun id -> id.Id.name = v) env with
      | [id] -> PVar id
      | [] -> failwith @@ "assign_id: unbounded variable (" ^ v ^ ")"
      | _ -> assert false
    end
    | PUnit -> PUnit
    | AInt i -> AInt i
    | Bool b -> Bool b
    | ANonDet -> ANonDet
    | PIf (p1, p2, p3) -> PIf (go env p1, go env p2, go env p3)
    | PEvent (e, p1) -> PEvent (e, go env p1)
    | PNonDet (p1, p2) -> PNonDet (go env p1, go env p2)
    | PApp (p1, p2) -> PApp (go env p1, go env p2)
    | AOp (e, ps) -> AOp (e, List.map (go env) ps)
    | Pred (e, ps) -> Pred (e, List.map (go env) ps)
    | And (p1, p2) -> And (go env p1, go env p2)
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | PLambda (args, p1) ->
      let args =
        List.map (fun (n, ty) ->
          let ty = 
            match ty with
            | None -> TVar (Id.gen ())
            | Some t -> t in
          Id.gen ~name:n ty
        ) args in
      let env' = (List.filter (fun id -> not @@ List.exists (fun n -> n.Id.name = id.Id.name) args) env) @ args in
      PLambda(args, go env' p1)
    | PLet ((n, ty), p1, p2) ->
      let p1 = go env p1 in
      let ty = 
        match ty with
        | None -> TVar (Id.gen ())
        | Some t -> t in
      let x = Id.gen ~name:n ty in
      let env' = (List.filter (fun id -> id.Id.name <> x.Id.name) env) @ [x] in
      PLet (x, p1, go env' p2)
  in
  List.map
    (fun (var, args, body) ->
      let body = go (global_env @ args) body in
      { var; body = body; args }
    )
    pred_args

let rec to_ty = function
  | R.TFunc (arg, body) -> Type.TyArrow ({name = ""; id = 0; ty = to_argty arg}, to_ty body)
  | R.TBool -> Type.TyBool ()
  | R.TUnit -> Type.TyBool ()
  | R.TInt -> assert false
  | R.TVar _ -> assert false
and to_argty = function
  | R.TInt -> Type.TyInt
  | t -> Type.TySigma (to_ty t)

let convert_all (program : R.raw_program) =
  let program =
    assign_id program
    |> infer_type
    |> List.map (fun func -> { func with R.body = convert_let func.R.body}) in
  let pred_args =
    let preds =
      List.map (fun {R.var} -> var) program |> List.filter (fun a -> a.Id.name <> "")
      |> Env.create in
    List.map (fun {R.var; args; body} ->
      let base_name = if var.Id.name = "" then None else Some var.Id.name in
      let body, new_rules = lambda_lift ?base_name preds (Env.create args) body in
      {R.var; args; body}::new_rules
    ) program
    |> List.flatten in
  let program_funcs =
    let preds =
      List.map (fun {R.var} -> { var with Id.ty = to_ty var.Id.ty }) pred_args |> List.filter (fun a -> a.Id.name <> "")
      |> Env.create in
    List.map (
      fun {R.var; args; body} ->
        let var = { var with Id.ty = to_ty var.Id.ty } in
        let args = List.map (fun id -> {id with Id.ty = to_argty id.Id.ty}) args in
        let body = convert body (Env.create args) preds in
        {Program.var; args; body}
    ) pred_args in
  match program_funcs |> List.partition (fun {Program.var;_} -> var.Id.name = "") with
  | [entry], xs ->
    let move_main_subs_tofirst xs =
      let firsts, seconds = List.partition (fun {Program.var} -> has_prefix var.name "lam_") xs in
      firsts @ seconds in
    entry.body, move_main_subs_tofirst xs
  | _ -> failwith "convert_all"
