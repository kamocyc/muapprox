open Hflmc2_syntax
module Env = Env_no_value

module Hflz = Hflmc2_syntax.Hflz

open Type_hflz7_def

let rec equal_type_modulo_flag ty1 ty2 =
  match ty1, ty2 with
  | TFunc (argty1, bodyty1, _), TFunc (argty2, bodyty2, _) ->
    equal_type_modulo_flag argty1 argty2 && equal_type_modulo_flag bodyty1 bodyty2
  | TBool, TBool -> true
  | TInt, TInt -> true
  | TVar _, TVar _ -> true (* TODO: *)
  | _ -> false

let get_free_variables phi =
  let rec go phi = match phi with
    | Bool _ -> []
    | Var v -> [v]
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Forall (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Exists (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | App (p1, p2) -> go p1 @ go p2
    | Arith a -> go_arith a
    | Pred (_, ps) -> List.map go_arith ps |> List.concat
  and go_arith a = match a with
    | Int _ -> []
    | Var v -> [v]
    | Op (_, ps) -> List.map go_arith ps |> List.concat
  in
  go phi

let get_thflz_type env phi =
  let rec go env phi = match phi with
    | Bool _ -> TBool
    | Var v -> begin
      match List.find_all (fun v' -> Id.eq v v') env with
      | [id'] -> begin
        print_endline "Var";
        print_endline @@ Id.to_string v;
        print_endline "id'.ty";
        print_endline @@ show_ptype @@ id'.ty;
        print_endline "v.ty";
        print_endline @@ show_ptype @@ v.ty; 
        assert (id'.ty = v.ty);
        v.ty
      end
      | _ -> assert false
    end
    | Or (p1, p2) ->
      assert (go env p1 = TBool);
      assert (go env p2 = TBool);
      TBool
    | And (p1, p2) ->
      assert (go env p1 = TBool);
      assert (go env p2 = TBool);
      TBool
    | Abs (x, p, lty) -> begin
      let ty = go (x::env) p in
      let f =
        match lty with
        | TFunc (p1, p2, f') ->
          assert (ty = p2);
          assert (x.Id.ty = p1);
          f'
        | _ -> assert false
      in
      TFunc (x.Id.ty, ty, f)
    end
    | Forall (x, body) ->
      go (x::env) body
    | Exists (x, body) ->
      go (x::env) body
    | App (p1, p2) -> begin
      let ty1 = go env p1 in
      let ty2 = go env p2 in
      match ty1 with
      | TFunc (t1, t2, _) -> begin
        assert (t1 = ty2);
        t2
      end
      | _ -> assert false
    end
    | Pred (_, args) ->
      List.iter (fun arg ->
        let ty = go_arith env arg in
        assert (ty = TInt);
      ) args;
      TBool
    | Arith a ->
      assert (go_arith env a = TInt);
      TInt
  and go_arith env a = match a with
    | Int _ -> TInt
    | Var v -> begin
      match List.find_all (fun v' -> Id.eq v' v) env with
      | [id'] ->
        assert (id'.ty = TInt);
        TInt
      | _ -> assert false
    end
    | Op (_, args) ->
      List.iter (fun arg ->
        let ty = go_arith env arg in
        assert (ty = TInt);
      ) args;
      TInt
  in
  go env phi

let check_thflz_type rules rec_flags =
  let filter_global_env rules rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    List.filter_map
      (fun {var; _} ->
        match List.find_opt (fun (x', _) -> Id.eq var x') nids with
        | Some (_, Recursive) ->
          Some ({var with ty=var.ty.inner_ty})
        | Some (_, NotRecursive) ->
          Some ({var with ty=var.ty.outer_ty})
        | None -> None
      )
      rules
  in
  List.iter
    (fun {var; body; _} ->
      let global_env = filter_global_env rules rec_flags var in
      (* print_endline "id to";
      print_endline @@ Id.to_string var;
      print_endline "get_thflz_type global_env body:";
      print_endline @@ show_ptype @@ get_thflz_type global_env body;
      print_endline "var.ty.inner_ty:";
      print_endline @@ show_ptype @@ var.ty.inner_ty; *)
      assert (get_thflz_type global_env body = var.ty.inner_ty)
    )
    rules

let rec ty_to_ptype ty =
  match ty with
  | Type.TyBool _ -> TBool
  | Type.TyArrow (arg, bodyty) ->
    TFunc (arg_to_ptype arg.ty, ty_to_ptype bodyty, dummy_use_flag)
and arg_to_ptype arg =
  match arg with
  | TyInt -> TInt
  | TySigma ty -> ty_to_ptype ty

let to_thflzs hes is_recursive =
  let rec go (phi : 'a Hflz.t): ptype thflz = match phi with
    | Bool b -> Bool b
    | Var v ->
      Var {v with ty=ty_to_ptype v.ty}
    | Or (p1, p2) ->
      Or (go p1, go p2)
    | And (p1, p2) ->
      And (go p1, go p2)
    | Abs (x, p) ->
      let ty = Hflz_util.get_hflz_type phi in
      Abs ({x with ty=arg_to_ptype x.ty}, go p, ty_to_ptype ty)
    | Forall (x, p) ->
      Forall ({x with ty=arg_to_ptype x.ty}, go p)
    | Exists (x, p) ->
      Exists ({x with ty=arg_to_ptype x.ty}, go p)
    | App (p1, p2) ->
      App (go p1, go p2)
    | Arith a ->
      Arith (go_arith a)
    | Pred (e, ps) ->
      Pred (e, List.map go_arith ps)
  and go_arith a = match a with
    | Int i -> Int i
    | Var v ->
      Var {v with ty=TInt}
    | Op (e, ps) ->
      Op (e, List.map go_arith ps)
  in
  List.map
    (fun {Hflz.var; body; fix} ->
      let fix =
        let (_, rec_f) = List.find (fun (id, _) -> Id.eq id var) is_recursive in
        if rec_f then begin
          match fix with
          | Greatest -> Greatest
          | Least -> Least
        end else NonRecursive in
      let body = go body in
      let var = { var with ty = {inner_ty = ty_to_ptype var.ty; outer_ty = ty_to_ptype var.ty}} in
      {var; body; fix}
    )
    hes

let generate_type_equal_constraint ty1 ty2 =
  let rec go ty1 ty2 =
    match ty1, ty2 with
    | TFunc (argty1, bodyty1, flag1), TFunc (argty2, bodyty2, flag2) ->
      (EF_Equal (flag1, flag2)) :: (go argty1 argty2) @ (go bodyty1 bodyty2)
    | TBool, TBool -> []
    | TInt, TInt -> []
    | _ -> assert false
  in
  go ty1 ty2

let rec assign_flags_to_type (ty : ptype) =
  match ty with
  | TFunc (tyarg, tybody, f) ->
    assert (f = dummy_use_flag);
    TFunc (assign_flags_to_type tyarg, assign_flags_to_type tybody, EFVar (Id.gen ())
    )
  | TInt -> TInt
  | TBool -> TBool
  | TVar v -> TVar v
  
let assign_flags (rules : ptype thes_rule list) : ptype thes_rule list =
  let rec go (raw : ptype thflz) : ptype thflz = match raw with
    | Bool b -> Bool b
    | Var v -> Var {v with ty = assign_flags_to_type v.ty}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, ty) -> Abs ({x with ty = assign_flags_to_type x.ty}, go p, assign_flags_to_type ty)
    | Forall (x, p) -> Forall ({x with ty=assign_flags_to_type x.ty}, go p)
    | Exists (x, p) -> Exists ({x with ty=assign_flags_to_type x.ty}, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith a
    | Pred (e, ps) -> Pred (e, ps)
  in
  List.map
    (fun {var; body; fix} ->
      let inner_ty = assign_flags_to_type var.ty.inner_ty in
      let outer_ty =
        match fix with
        | Least ->
          let rec go = function
            | TFunc (argty, bodyty, _) -> TFunc (argty, go bodyty, TUse)
            | TBool -> TBool
            | _ -> assert false
          in
          go inner_ty
        | Greatest | NonRecursive -> inner_ty
      in
      let var = {var with ty = {inner_ty; outer_ty}} in
      let body = go body in
      { var; body; fix}
    )
    rules

let generate_flag_constraints (rules : ptype thes_rule list) (rec_flags : ('a Type.ty Id.t * ('a Type.ty Id.t * recursive_flag) list) list) : use_flag_constraint list =
  let filter_env env fvs =
    List.fold_left
      (fun env' fv ->
        let v = Env.lookup fv env in
        Env.update [v] env'
      )
      (Env.create [])
      fvs
  in
  let rec gen (env : (ptype * use_flag) Env.t) (raw : ptype thflz)
      : ptype * use_flag_constraint list = match raw with
    | Bool _ -> (TBool, [])
    | Var v ->
      let id = Env.lookup v env in
      let ty, _ = id.ty in
      assert (equal_type_modulo_flag ty v.ty);
      let c = generate_type_equal_constraint ty v.ty in
      (ty, c)
    | Or (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool);
      assert (t2 = TBool);
      (TBool, f1 @ f2)
    | And (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool);
      assert (t2 = TBool);
      (TBool, f1 @ f2)
    | Abs (arg, body, ty_aux) -> begin
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, f = gen env body in
      let ty = TFunc (arg.Id.ty, t, EFVar flag) in
      assert (equal_type_modulo_flag ty_aux ty);
      let c = generate_type_equal_constraint ty_aux ty in
      (ty, c @ f)
    end
    | Forall (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, f = gen env body in
      (t, f)
    | Exists (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, EFVar flag)}] env in
      let t, f = gen env body in
      (t, f)
    | App (p1, p2) -> begin
      let t1, f1 = gen env p1 in
      let tyarg, tybody, flag_a1 =
        match t1 with
        | TFunc (tyarg, tybody, f) -> tyarg, tybody, f
        | _ -> assert false
      in
      let t2, flag_constrs =
        let fvs = get_free_variables p2 in
        let env' = filter_env env fvs in
        let flag_constrs =
          Env.to_list env'
          |> List.map (fun id -> snd id.Id.ty)
          |> List.map (fun f -> EF_Le (flag_a1, f)) in
        let t2, f2 = gen env' p2 in
        t2, f2 @ flag_constrs
      in
      assert (equal_type_modulo_flag tyarg t2);
      let c = generate_type_equal_constraint tyarg t2 in
      (tybody, c @ f1 @ flag_constrs)
    end
    | Arith _ ->
      (TInt, [])
    | Pred _ ->
      (TBool, [])
  in
  let global_env =
    List.map (fun {var; _} -> (var, EFVar (Id.gen ()))) rules in
  let filter_global_env global_env rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    Env.create @@
    List.filter_map
      (fun (var, var_flag) ->
        match List.find_opt (fun (x', _) -> Id.eq var x') nids with
        | Some (_, Recursive) ->
          Some {var with ty=(var.ty.inner_ty, var_flag)}
        | Some (_, NotRecursive) ->
          Some {var with ty=(var.ty.outer_ty, var_flag)}
        | None -> None
      )
      global_env
  in
  List.map
    (fun { var; body; fix=_fix } ->
      let global_env = filter_global_env global_env rec_flags var in
      let ty, flag_constraints = gen global_env body in
      assert (equal_type_modulo_flag ty var.ty.inner_ty);
      let c = generate_type_equal_constraint ty var.ty.inner_ty in
      c @ flag_constraints
    )
    rules
  |> List.flatten

let rec subst_flags_type ty subst =
  match ty with
  | TFunc (ty1, ty2, f) -> begin
    let f =
      match f with
      | EFVar id -> begin
        match List.find_opt (fun (id', _) -> Id.eq id id') subst with
        | Some (_, f') -> f'
        | None -> f
      end
      | f -> f
      in
    TFunc (subst_flags_type ty1 subst, subst_flags_type ty2 subst, f)
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
  
let subst_flags_program (rules : ptype thes_rule list) (subst : (unit Id.t * use_flag) list) : ptype thes_rule list =
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=subst_flags_type v.ty subst}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, ty) -> Abs ({x with ty=subst_flags_type x.ty subst}, go p, subst_flags_type ty subst)
    | Forall (x, p) -> Forall ({x with ty=subst_flags_type x.ty subst}, go p)
    | Exists (x, p) -> Exists ({x with ty=subst_flags_type x.ty subst}, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var; body; fix} ->
      let var = { var with ty = {inner_ty = subst_flags_type var.ty.inner_ty subst; outer_ty = subst_flags_type var.ty.outer_ty subst }} in
      let body = go body in
      { var; body; fix }
    )
    rules

let rec set_not_use_in_undetermined_flags_ty ty =
  match ty with
  | TFunc (argty, bodyty, f) -> begin
    let f =
      match f with
      | EFVar _ -> TNotUse
      | f -> f in
    TFunc (set_not_use_in_undetermined_flags_ty argty, set_not_use_in_undetermined_flags_ty bodyty, f)
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
    
let set_not_use_in_undetermined_flags rules =
  let rec go (phi : ptype thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=set_not_use_in_undetermined_flags_ty v.ty}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, ty) -> Abs ({x with ty=set_not_use_in_undetermined_flags_ty x.ty}, go p, set_not_use_in_undetermined_flags_ty ty)
    | Forall (x, p) -> Forall ({x with ty=set_not_use_in_undetermined_flags_ty x.ty}, go p)
    | Exists (x, p) -> Exists ({x with ty=set_not_use_in_undetermined_flags_ty x.ty}, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var; body; fix} ->
      let var = { var with ty = {inner_ty = set_not_use_in_undetermined_flags_ty var.ty.inner_ty; outer_ty = set_not_use_in_undetermined_flags_ty var.ty.outer_ty }} in
      let body = go body in
      { var; body; fix }
    )
    rules
    
(* let rec to_ty = function
  | TFunc (arg, body, _) -> Type.TyArrow ({name = ""; id = 0; ty = to_argty arg}, to_ty body)
  | TBool -> Type.TyBool ()
  | TInt -> assert false
  | TVar _ -> assert false
and to_argty = function
  | TInt -> Type.TyInt
  | t -> Type.TySigma (to_ty t) *)
  
let infer_thflz_type (rules : ptype thes_rule list) rec_flags: ptype thes_rule list =
  let rules = assign_flags rules in
  let flag_constraints = generate_flag_constraints rules rec_flags in
  let flag_substitution = Type_hflz7_unify_flags.unify_flags flag_constraints in
  let rules = subst_flags_program rules flag_substitution in
  let rules = set_not_use_in_undetermined_flags rules in
  rules

let get_recursivity (rules : 'a Type.ty Hflz.hes_rule list) =
  let preds, graph = Hflz_util.get_dependency_graph rules in
  List.map
    (fun (i, pred) ->
      let reachables = Mygraph.reachable_nodes_from ~start_is_reachable_initially:false i graph in
      match List.find_opt (fun r -> r = i) reachables with
      | Some _ -> (pred, true)
      | None -> (pred, false)
    )
    preds
  
let construct_recursion_flags (rules : 'a Type.ty Hflz.hes_rule list) =
  let preds, graph = Hflz_util.get_dependency_graph rules in
  (* Depth first search *)
  let rec dfs seen current =
    let nids = Mygraph.get_next_nids current graph in
    (* 既に見たなら、「再帰」とフラグを付ける *)
    List.map
      (fun nid ->
        match List.find_opt (fun s -> s = nid) seen with
        | Some _ -> [(current, (nid, Recursive))]
        | None ->
          let map = dfs (nid::seen) nid in
          (current, (nid, NotRecursive)) :: map
      )
      nids
    |> List.flatten
  in
  let map = dfs [0] 0 in
  let map =
    Hflmc2_util.group_by (fun (key, _) -> key) map
    |> Hflmc2_util.list_of_hashtbl
    |> List.map (fun (k, vs) -> (k, List.map snd vs)) in
  let map =
    List.map
      (fun (k, flags) ->
        let flags =
          Hflmc2_util.group_by (fun (key, _) -> key) flags
          |> Hflmc2_util.list_of_hashtbl
          |> List.map (fun (k, vs) -> (k, List.map snd vs)) in
        let flag =
          List.map
            (fun (nid, flags) ->
              (* prioritize NotRecursive *)
              match List.find_opt (fun f -> match f with NotRecursive -> true | Recursive -> false) flags with
              | Some _ -> (nid, NotRecursive)
              | None -> (nid, Recursive)
            )
            flags in
        (k, flag)
      )
      map
  in
  let map =
    List.map
      (fun (i, id) ->
        match List.find_opt (fun (j, _) -> i = j) map with
        | Some (_, nids) ->
          (id, List.map (fun (k, v) -> let (_, id) = List.find (fun (i, _) -> i = k) preds in (id, v)) nids)
        | None -> (id, [])
      )
      preds
  in
  print_endline "recursion flags:";
  print_endline @@ Hflmc2_util.show_pairs Id.to_string (fun flags -> Hflmc2_util.show_pairs Id.to_string show_recursive_flag flags) map;
  map

let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let is_recursive = get_recursivity rules in
  let rec_flags = construct_recursion_flags rules in
  let rules = to_thflzs rules is_recursive in
  print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules;
  print_endline "to_thflz (simple)";
  print_endline @@
    Hflmc2_util.fmt_string
      (Print_temp.hflz_hes pp_ptype) rules;
  let rules = infer_thflz_type rules rec_flags in
  let () =
    print_endline "result:";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    save_to_file "tmp_t7.txt" @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    check_thflz_type rules rec_flags
    in
  print_endline "infer_thflz_type (2)";
  print_endline @@ show_s_thes_rules rules;
  print_endline "type hflz 7";
  (* let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes; *)
  (* print_endline @@ Hflz.show_hes Type.pp_simple_ty hes;  *)
  hes
