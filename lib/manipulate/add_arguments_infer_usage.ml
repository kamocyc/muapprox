open Hflmc2_syntax
module Env = Env_no_value

open Add_arguments_tuple

let generate_type_equal_constraint ty1 ty2 =
  let rec go ty1 ty2 =
    match ty1, ty2 with
    | TFunc (argtys1, bodyty1), TFunc (argtys2, bodyty2) ->
      (List.map
        (fun ((argty1, tag1), (argty2, tag2)) ->
          T.EF_Equal (tag1, tag2) :: go argty1 argty2
        )
        (List.combine argtys1 argtys2)
      |> List.flatten)
      @ (go bodyty1 bodyty2)
    | TBool, TBool -> []
    | TInt, TInt -> []
    | _ -> assert false
  in
  go ty1 ty2

let rec assign_flags_to_type (ty : ptype2) =
  match ty with
  | TFunc (tyargs, tybody) ->
    TFunc (
      List.map
        (fun (ty, t) ->
          assert (t = T.dummy_use_flag);
          assign_flags_to_type ty,
          T.EFVar (Id.gen ()))
        tyargs,
      assign_flags_to_type tybody
    )
  | TInt -> TInt
  | TBool -> TBool
  | TVar v -> TVar v
  
let assign_flags (rules : ptype2 thes_rule list) : ptype2 thes_rule_in_out list =
  let rec go (raw : ptype2 thflz2) : ptype2 thflz2 = match raw with
    | Bool b -> Bool b
    | Var v -> Var {v with ty = assign_flags_to_type v.ty}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty = assign_flags_to_type x.Id.ty}) xs, go p, assign_flags_to_type ty)
    | Forall (x, p) -> Forall ({x with ty=assign_flags_to_type x.ty}, go p)
    | Exists (x, p) -> Exists ({x with ty=assign_flags_to_type x.ty}, go p)
    | App (p1, ps) -> App (go p1, List.map go ps)
    | Arith a -> Arith a
    | Pred (e, ps) -> Pred (e, ps)
  in
  List.map
    (fun {var; body; fix} ->
      let inner_ty = assign_flags_to_type var.ty in
      let outer_ty =
        match fix with
        | Least ->
          let rec go = function
            | TFunc (argty, bodyty) ->
              TFunc (
                List.map (fun (arg, _) -> arg, T.TUse) argty,
                go bodyty
              )
            | TBool -> TBool
            | _ -> assert false
          in
          go inner_ty
        | Greatest | NonRecursive -> inner_ty
      in
      let var = {var with ty = {T.inner_ty; outer_ty}} in
      let body = go body in
      { var_in_out = var; body; fix}
    )
    rules

let generate_flag_constraints (rules : ptype2 thes_rule_in_out list) (rec_flags : ('a Type.ty Id.t * ('a Type.ty Id.t * T.recursive_flag) list) list) : T.use_flag_constraint list =
  let filter_env env fvs =
    List.fold_left
      (fun env' fv ->
        let v = Env.lookup fv env in
        Env.update [v] env'
      )
      (Env.create [])
      fvs
  in
  let rec gen (env : (ptype2 * T.use_flag) Env.t) (raw : ptype2 thflz2)
      : ptype2 * T.use_flag_constraint list = match raw with
    | Bool _ -> (TBool, [])
    | Var v ->
      let id = Env.lookup v env in
      let ty, _ = id.ty in
      (ty, generate_type_equal_constraint ty v.ty)
    | Or (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool && t2 = TBool);
      (TBool, f1 @ f2)
    | And (p1, p2) ->
      let t1, f1 = gen env p1 in
      let t2, f2 = gen env p2 in
      assert (t1 = TBool && t2 = TBool);
      (TBool, f1 @ f2)
    | Abs (args, body, ty_aux) -> begin
      let arg_tags = List.map (fun arg -> (arg, T.EFVar (Id.gen ()))) args in
      let env = Env.update (List.map (fun (arg, tag) -> {arg with Id.ty = (arg.Id.ty, tag)}) arg_tags) env in
      let t, fc = gen env body in
      let ty = TFunc (List.map (fun (arg, tag) -> (arg.Id.ty, tag)) arg_tags, t) in
      (ty, (generate_type_equal_constraint ty_aux ty) @ fc)
    end
    | Forall (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, T.EFVar flag)}] env in
      let t, f = gen env body in
      (t, f)
    | Exists (arg, body) ->
      let flag = Id.gen () in
      let env = Env.update [{arg with ty = (arg.ty, T.EFVar flag)}] env in
      let t, f = gen env body in
      (t, f)
    | App (p1, ps) -> begin
      let t1, f1 = gen env p1 in
      let tyargs, tybody =
        match t1 with
        | TFunc (tyargs, tybody) -> tyargs, tybody
        | _ -> assert false
      in
      let flag_constrs =
        List.map
          (fun (p2, (ty2, tag)) ->
            let fvs = get_free_variables p2 in
            let env' = filter_env env fvs in
            let flag_constrs =
              Env.to_list env'
              |> List.map (fun id -> snd id.Id.ty)
              |> List.map (fun f -> T.EF_Le (tag, f)) in
            let t2, f2 = gen env' p2 in
            f2 @ flag_constrs @ (generate_type_equal_constraint ty2 t2)
          )
          (List.combine ps tyargs)
        |> List.flatten
      in
      (tybody, f1 @ flag_constrs)
    end
    | Arith _ -> (TInt, [])
    | Pred _ -> (TBool, [])
  in
  let global_env =
    List.map (fun {var_in_out; _} -> (var_in_out, T.EFVar (Id.gen ()))) rules in
  let filter_global_env global_env rec_flags var =
    let (_, nids) = List.find (fun (k, _) -> Id.eq k var) rec_flags in
    Env.create @@
    List.filter_map
      (fun (var, var_flag) ->
        match List.find_opt (fun (x', _) -> Id.eq var x') nids with
        | Some (_, T.Recursive) ->
          Some {var with ty=(var.ty.T.inner_ty, var_flag)}
        | Some (_, NotRecursive) ->
          Some {var with ty=(var.ty.outer_ty, var_flag)}
        | None -> None
      )
      global_env
  in
  List.map
    (fun { var_in_out; body; fix=_fix } ->
      let global_env = filter_global_env global_env rec_flags var_in_out in
      let ty, flag_constraints = gen global_env body in
      (generate_type_equal_constraint ty var_in_out.ty.inner_ty) @ flag_constraints
    )
    rules
  |> List.flatten

let rec subst_flags_type ty subst =
  let subst_flag f =
    match f with
      | T.EFVar id -> begin
        match List.find_opt (fun (id', _) -> Id.eq id id') subst with
        | Some (_, f') -> f'
        | None -> f
      end
      | f -> f
  in
  match ty with
  | TFunc (tys, ty2) -> begin
    TFunc (
      List.map
        (fun (ty1, tag) ->
          subst_flags_type ty1 subst,
          subst_flag tag
        )
        tys,
      subst_flags_type ty2 subst
    )
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
  
let subst_flags_program (rules : ptype2 thes_rule_in_out list) (subst : (unit Id.t * T.use_flag) list) : ptype2 thes_rule_in_out list =
  let rec go (phi : ptype2 thflz2) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=subst_flags_type v.ty subst}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty=subst_flags_type x.Id.ty subst}) xs, go p, subst_flags_type ty subst)
    | Forall (x, p) -> Forall ({x with ty=subst_flags_type x.ty subst}, go p)
    | Exists (x, p) -> Exists ({x with ty=subst_flags_type x.ty subst}, go p)
    | App (p1, p2) -> App (go p1, List.map go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var_in_out; body; fix} ->
      let var_in_out = { var_in_out with ty = {T.inner_ty = subst_flags_type var_in_out.ty.inner_ty subst; outer_ty = subst_flags_type var_in_out.ty.outer_ty subst }} in
      let body = go body in
      { var_in_out; body; fix }
    )
    rules

let rec set_not_use_in_undetermined_flags_ty ty =
  match ty with
  | TFunc (argtys, bodyty) -> begin
    TFunc (
      List.map
        (fun (argty, tag) ->
          set_not_use_in_undetermined_flags_ty argty,
          let tag =
            match tag with
            | T.EFVar _ -> T.TNotUse
            | tag -> tag in
          tag
        )
        argtys,
      set_not_use_in_undetermined_flags_ty bodyty
    )
  end
  | TBool -> TBool
  | TInt -> TInt
  | TVar _ -> assert false
    
let set_not_use_in_undetermined_flags rules =
  let rec go (phi : ptype2 thflz2) = match phi with
    | Bool b -> Bool b
    | Var v -> Var {v with ty=set_not_use_in_undetermined_flags_ty v.ty}
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (xs, p, ty) -> Abs (List.map (fun x -> {x with Id.ty=set_not_use_in_undetermined_flags_ty x.Id.ty}) xs, go p, set_not_use_in_undetermined_flags_ty ty)
    | Forall (x, p) -> Forall ({x with ty=set_not_use_in_undetermined_flags_ty x.ty}, go p)
    | Exists (x, p) -> Exists ({x with ty=set_not_use_in_undetermined_flags_ty x.ty}, go p)
    | App (p1, p2) -> App (go p1, List.map go p2)
    | Arith a -> Arith a
    | Pred (op, ps) -> Pred (op, ps)
  in
  List.map
    (fun {var_in_out; body; fix} ->
      let var_in_out = { var_in_out with ty = {T.inner_ty = set_not_use_in_undetermined_flags_ty var_in_out.ty.inner_ty; outer_ty = set_not_use_in_undetermined_flags_ty var_in_out.ty.outer_ty }} in
      let body = go body in
      { var_in_out; body; fix }
    )
    rules

let infer_thflz_type (rules : ptype2 thes_rule list) rec_flags: ptype2 thes_rule_in_out list =
  let rules = assign_flags rules in
  let flag_constraints = generate_flag_constraints rules rec_flags in
  let flag_substitution = Add_arguments_unify_flags.unify_flags flag_constraints in
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
        | Some _ -> [(current, (nid, T.Recursive))]
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
              match List.find_opt (fun f -> match f with T.NotRecursive -> true | Recursive -> false) flags with
              | Some _ -> (nid, T.NotRecursive)
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
  (* print_endline "recursion flags:";
  print_endline @@ Hflmc2_util.show_pairs Id.to_string (fun flags -> Hflmc2_util.show_pairs Id.to_string show_recursive_flag flags) map; *)
  map

let show_id_map id_map show_f = 
  "{" ^
  (IdMap.to_alist id_map
  |> List.map (fun (id, vt) -> "" ^ Id.to_string id ^ "=" ^ show_f vt)
  |> String.concat ", ") ^
  "}"

module Print_temp = struct
  include Print_temp
  
  let hflz_hes_rule : (Print.Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf {var; body; fix} ->
      let args, body = get_args body in
      Fmt.pf ppf "@[<2>%s %a =%s@ %a@]"
        (Id.to_string var)
        (Print.pp_print_list
          ~pp_sep:Print_syntax.PrintUtil.fprint_space
          (fun ppf (args, tts) ->
            (* if !show_tag_as_separator then
              fprintf ppf "(%s : (%a){%s})" (Id.to_string arg) (format_ty_ Prec.zero) arg.Id.ty (show_use_flag f2)
            else *)
              Print.fprintf ppf "(%s : %s)"
                (show_list Id.to_string args)
                (Hflmc2_util.fmt_string pp_ptype2_arg tts)
              (* fprintf ppf "(%s : %a)" (Id.to_string arg) (format_ty_ Prec.zero) arg.Id.ty *)
          )
        )
        args
        (show_fixpoint fix)
        (hflz_ thflz_to_ptype format_ty_) body

  let hflz_hes :  (Print.Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
end
