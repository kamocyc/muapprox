open Hflmc2_syntax
module Env = Env_no_value

open Type_hflz7_def

let rec equal_type_modulo_flag ty1 ty2 =
  match ty1, ty2 with
  | TFunc (argty1, bodyty1, _), TFunc (argty2, bodyty2, _) ->
    equal_type_modulo_flag argty1 argty2 && equal_type_modulo_flag bodyty1 bodyty2
  | TBool, TBool -> true
  | TInt, TInt -> true
  | TVar _, TVar _ -> true (* TODO: *)
  | _ -> false

let get_thflz_type env phi =
  let rec go env phi = match phi with
    | Bool _ -> TBool
    | Var v -> begin
      match List.find_all (fun v' -> Id.eq v v') env with
      | [id'] -> begin
        (* print_endline "Var";
        print_endline @@ Id.to_string v;
        print_endline "id'.ty";
        print_endline @@ show_ptype @@ id'.ty;
        print_endline "v.ty";
        print_endline @@ show_ptype @@ v.ty;  *)
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

let check_thflz_type rules =
  List.iter
    (fun {var; body; _} ->
      let global_env = List.map (fun {var; _} -> {var with ty=var.ty.inner_ty}) rules in
      assert (var.ty.outer_ty = var.ty.inner_ty);
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
      let outer_ty = inner_ty in
      let var = {var with ty = {inner_ty; outer_ty}} in
      let body = go body in
      { var; body; fix}
    )
    rules

let generate_flag_constraints rules =
  let rec gen env apps (phi : ptype thflz)
      : ptype * use_flag_constraint list = match phi with
    | App (p1, p2) -> begin
      let ty2, c2 = gen env [] p2 in
      let ty1, c1 = gen env (p2::apps) p1 in
      match ty1 with
      | TFunc (argty, bodyty, _) ->
        (* print_endline "App 2";
        print_endline @@ show_ptype argty;
        print_endline @@ show_ptype ty2; *)
        let c = generate_type_equal_constraint argty ty2 in
        bodyty, c1 @ c2 @ c
      | _ -> assert false
    end
    | _ -> begin
      let ty, c =
        match phi with
        | App _ -> assert false
        | Bool _ -> (TBool, [])
        | Var v ->
          let id = Env.lookup v env in
          let ty = id.ty in
          (ty, generate_type_equal_constraint ty v.ty)
        | Or (p1, p2) ->
          let ty1, c1 = gen env [] p1 in
          let ty2, c2 = gen env [] p2 in
          assert (ty1 = TBool && ty2 = TBool);
          (TBool, c1 @ c2)
        | And (p1, p2) ->
          let ty1, c1 = gen env [] p1 in
          let ty2, c2 = gen env [] p2 in
          assert (ty1 = TBool && ty2 = TBool);
          (TBool, c1 @ c2)
        | Abs (arg, body, ty_aux) -> begin
          let tag = Id.gen () in
          let env = Env.update [arg] env in
          let ty1, c1 = gen env [] body in
          let ty = TFunc (arg.Id.ty, ty1, EFVar tag) in
          (ty, (generate_type_equal_constraint ty_aux ty) @ c1)
        end
        | Forall (arg, body) ->
          let env = Env.update [arg] env in
          let ty, c = gen env [] body in
          (ty, c)
        | Exists (arg, body) ->
          let env = Env.update [arg] env in
          let ty, c = gen env [] body in
          (ty, c)
        | Arith _ -> (TInt, [])
        | Pred _ -> (TBool, [])
      in
      let c' =
        match apps with
        | _::_ -> begin
          (* set T in the last application *)
          let rec go ty1 apps = match ty1, apps with
            | TFunc (_, bodyty, t), [_] ->
              EF_Equal (t, TUse), bodyty
            | TFunc (_, bodyty, _), (_::apps) ->
              go bodyty apps
            | _ -> assert false
          in
          (* print_endline "App";
          print_endline @@ show_ptype ty;
          print_endline @@ Hflmc2_util.show_list (Hflmc2_util.fmt_string (Print_temp.hflz pp_ptype)) apps; *)
          let c', _ = go ty apps in
          (c' :: c)
        end
        | [] -> [] in
      ty, c @ c'
    end
  in
  let global_env =
    Env.create @@ List.map (fun {var; _} -> {var with ty = var.ty.inner_ty}) rules in
  List.map
    (fun {var; body; _} ->
      let ty, c = gen global_env [] body in
      let c1 = generate_type_equal_constraint ty var.Id.ty.inner_ty in
      c @ c1
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
  
let infer_thflz_type (rules : ptype thes_rule list): ptype thes_rule list =
  let rules = assign_flags rules in
  let flag_constraints = generate_flag_constraints rules in
  let flag_substitution = Type_hflz7_unify_flags.unify_flags flag_constraints in
  let rules = subst_flags_program rules flag_substitution in
  let rules = set_not_use_in_undetermined_flags rules in
  rules

let show_id_map id_map show_f = 
  "{" ^
  (IdMap.to_alist id_map
  |> List.map (fun (id, vt) -> "" ^ Id.to_string id ^ "=" ^ show_f vt)
  |> String.concat ", ") ^
  "}"

let infer (hes : 'a Hflz.hes) : Type.simple_ty Hflz.hes =
  Type_hflz7_def.show_tag_as_separator := true;
  let original_rules = Hflz.merge_entry_rule hes in
  let is_recursive = get_recursivity original_rules in
  let rules = to_thflzs original_rules is_recursive in
  (* print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules;
  print_endline "to_thflz (simple)";
  print_endline @@
    Hflmc2_util.fmt_string
      (Print_temp.hflz_hes pp_ptype) rules; *)
  let rules = infer_thflz_type rules in
  let () =
    print_endline "result (infer partial):";
    print_endline @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    (* print_endline "result (full)";
    print_endline @@ show_s_thes_rules rules; *)
    save_to_file "tmp_t7.txt" @@
      Hflmc2_util.fmt_string
        (Print_temp.hflz_hes pp_ptype) rules;
    check_thflz_type rules;
    in
  (* print_endline "type hflz 7"; *)
  (* let rules = to_hflz rules in
  let hes = Hflz.decompose_entry_rule rules in
  Hflz_typecheck.type_check hes; *)
  let a = Type_hflz7_tuple.to_thflz2 rules in
  Type_hflz7_tuple.check_thflz2_type a;
  Type_hflz7_def.show_tag_as_separator := false;
  hes
